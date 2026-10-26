import Std.Data.HashSet
import KaterCert.Whole

/-!
# Extensibility

Kater's export checks that GenMC can add an event to a consistent graph
without breaking an acyclicity or coherence constraint
(`Checker::decideExtensibility`, `doc/verification.md`, Extensibility). It
takes the automaton of the constraint, finds the steps a cycle can leave
an event GenMC adds by (`exitsToCheck`), builds the automaton of the words
from the event along each such step to the end of its word (`toEndOfWord`),
and decides that each word is in `pporf ; any*`, or, for a cycle of
coherence that leaves the event where its word begins, in `po+ ; (rf | mo
| fr)+` too (`decideExitWords`). Its evidence
(`ReadChain.Extensibility`) has the constraint's automaton and each
inclusion it decided, which this checks: the words automaton is within the
automaton of the final check, the chain of the right-hand side checks as
for assertions (`Whole.right`), and the certificate (`Whole.final`).
`checkWords_sound` proves that the words then denote no more than the
right-hand side.

How the words came from the constraint is checked too (`checkCycles`): the
constraint's automaton, as Kater read its cycles, against Lean's automaton
of the constraint, and the words Lean builds from it again against Kater's.
`Cycles.lean` proves what that gives: a cycle through an event GenMC adds
either visits it where it can do without it, or reads a word of the words
automaton from it.

Lean's construction of the words follows Kater's (`exitsToCheck`,
`toEndOfWord`) but where it can be simpler and is no less safe: it does not
cap the predicates an exit has read at the eight a `PredicateSet` holds
(`fitTogether`), so its exits check more and its words are fewer; it rules
out a predicate's letter where Lean's theory says no event passes its
checks with those read (`Theory.unsat`), where Kater asks `composes`; its
search goes on into a third word, which a constraint whose automaton
accepts no word of predicates alone never does; and it keeps the states of
the words automaton that `removeDeadStates` drops. Lean's words have to be
within Kater's, so a difference that made them more would show as a
rejection.

This mirrors the C++ regions `ExtensibilityEvidence` (`src/Checker.hpp`),
`exitsToCheck` and `decideExtensibility` (`src/Checker.cpp`):
`scripts/check-mirrors.sh` reports when they change.
-/

namespace KaterCert

universe u

open ReadChain

namespace Extensible

/-! ## The right-hand sides -/

/-- A builtin relation as an expression. -/
def bare (r : Builtin.Rel) : Exp := .label (Exp.bareLabel r.id)

/-- `po+ ; (rf | mo | fr)+`: a cycle that goes back to the event this way is
a `po` path to an access of its location, and `eco` back. -/
def backToEvent : Exp :=
  .seq (.plus (bare .po)) (.plus (.alt (.alt (bare .rf) (bare .mo)) (bare .fr)))

/-- `pporf ; any*`, and with `back` also `po+ ; (rf | mo | fr)+`: the
right-hand side `decideExitWords` decides, as Kater's expressions read. -/
def rhsOf (pporf : Exp) (back : Bool) : Exp :=
  if back then .alt (.seq pporf (.star (bare .any))) backToEvent
  else .seq pporf (.star (bare .any))

/-- The alternatives of an expression. -/
def altList : Exp → List Exp
  | .alt a b => altList a ++ altList b
  | e => [e]

@[simp] theorem altList_bare (r : Builtin.Rel) : altList (bare r) = [bare r] := rfl

/-- GenMC's prefix relation, `(ppo | rfe | tc | tj | lin)+`. -/
def pporfOf (ppo : Exp) : Exp :=
  .plus (.alt (.alt (.alt (.alt ppo (bare .rfe)) (bare .tc)) (bare .tj)) (bare .lin))

/-- Whether `pporf` is `(ppo | rfe | tc | tj | lin)+` as Kater's
`createPPORF` makes it: the same alternatives, flattened, without
duplicates. -/
def pporfOk (ppo pporf : Exp) : Bool :=
  match pporf with
  | .plus a =>
    let extra := altList ppo ++ [bare .rfe, bare .tc, bare .tj, bare .lin]
    (altList a).all (extra.contains ·) && extra.all ((altList a).contains ·)
  | _ => false

/-! ## The inclusions of the words -/

/-- An inclusion of words checks: Kater's words automaton is within the
automaton of the final check, the start of the chain within Lean's
automaton of the right-hand side, each pass of the chain within the one
before it, without a rotation, and the certificate is of the two last
automata. -/
def checkWords (θ : Theory) (hyps : List Constraint) (w : WordsInclusion) : Except String Unit :=
  if !Guarded.prove θ w.words.nfa w.final.nfa false (some w.final.origins) then
    .error "the words are not within the left automaton of the final check"
  else if !Guarded.prove θ w.chain.start (Thompson.nfa w.rhs) false then
    .error "Kater's right automaton is not within the right-hand side"
  else match Whole.right θ hyps w.chain.start
      (Whole.withOrigins w.chain.passes w.chainOrigins.tail) with
    | .error e => .error e
    | .ok (R, rot) =>
      if rot then .error "a rotation in the chain of a words inclusion"
      else Whole.final θ w.cert w.final.nfa R

/-- The words automata are those of the check: one, whose words leave the
event within their word, or for coherence (`single`) two, the second of
which has the words that go back to the event. -/
def shapeOk (single : Bool) (ws : List WordsInclusion) : Bool :=
  match single, ws with
  | false, [w] => !w.backToEvent
  | true, [w₁, w₂] => !w₁.backToEvent && w₂.backToEvent
  | _, _ => false

/-- The inclusions of an extensibility check: the module's declarations are
well-formed, `pporf` is the module's, the words automata are those of the
check, and each decides the right-hand side it should and checks. -/
def checkInclusions (x : Extensibility) : Except String Unit :=
  if !x.module.decls.wf then .error "the per-location variants are not well-formed"
  else if !pporfOk x.ppo x.pporf then .error "pporf is not (ppo | rfe | tc | tj | lin)+"
  else if !shapeOk x.single x.words then .error "the words automata are not those of the check"
  else go x.words
where
  go : List WordsInclusion → Except String Unit
    | [] => .ok ()
    | w :: ws =>
      if w.rhs != rhsOf x.pporf w.backToEvent then
        .error "a words inclusion decides another right-hand side"
      else match checkWords (Theory.ofDecls x.module.decls) (Whole.hypsOf x.module.assumptions) w with
        | .error e => .error e
        | .ok () => go ws

/-! ## The words, as Lean builds them

Kater takes the steps a cycle can leave an event by from the constraint's
automaton, as `exitsToCheck` reads it, and builds the words from them
(`toEndOfWord`). Lean builds them again from the same automaton: for each
state a relation's letter enters, the configurations that the predicates'
letters at the event, and the end of a word, reach from it (`reach`, a
search, whose result `closed` verifies), the steps out of those, and of
those the ones the check asks about (`toCheck`): not by a step within `rf`,
`mo` or `fr`, not checking what an event GenMC adds cannot be (`addable`),
and not skippable after each step into the state (`canSkip`). The words
automaton it builds of them (`words`) has to be within Kater's. -/

/-- What an event GenMC adds alone is: not part of an RMW, not a thread
start, not a thread create (which GenMC adds with its thread's start). -/
def addable : List Predicate :=
  [⟨Builtin.Pred.NEXCL.id, false⟩, ⟨Builtin.Pred.TC.id, true⟩, ⟨Builtin.Pred.TB.id, true⟩]

/-- A configuration of the search for the exits of a state: a state, the
predicates read of the event since the step into it, and whether the cycle
went on into the next word. -/
abbrev Conf := Nat × List Predicate × Bool

/-- The configurations a move at the event takes `c` to: a predicate's
letter, if its checks can hold with those read, or the end of a word, into
the start of the next. -/
def moves (θ : Theory) (N : NFA Label) (c : Conf) : List Conf :=
  ((N.trans c.1).filterMap fun t =>
    if t.1.rel.isNone && !θ.unsat (Guarded.union c.2.1 t.1.pre) then
      some (t.2, Guarded.union c.2.1 t.1.pre, c.2.2)
    else none) ++
  (if N.isAccepting c.1 then N.start.map fun s => (s, c.2.1, true) else [])

/-- Whether `S` is closed under `moves`, up to configurations that read
fewer predicates. -/
def closed (θ : Theory) (N : NFA Label) (S : List Conf) : Bool :=
  S.all fun c => (moves θ N c).all fun c' =>
    S.any fun c'' => c''.1 == c'.1 && c''.2.2 == c'.2.2 && Guarded.subTests c''.2.1 c'.2.1

/-- The configurations `moves` reach from `c`: a search, with fuel, whose
result `closed` checks. -/
def reach (θ : Theory) (N : NFA Label) (c : Conf) (fuel : Nat := 100000) : List Conf := Id.run do
  let mut seen : Std.HashSet Conf := {}
  let mut work : List Conf := [c]
  let mut out : List Conf := []
  for _ in [0:fuel] do
    match work with
    | [] => break
    | c :: rest =>
      work := rest
      if seen.contains c then continue
      seen := seen.insert c
      out := c :: out
      work := moves θ N c ++ work
  return out

/-- A step a cycle can leave the event it visits by (Kater's `Exit`): what
it checked of the event first, the letter, the state it leads to, and
whether it began the next word. -/
structure Exit where
  preds : List Predicate
  label : Label
  dest : Nat
  wraps : Bool
  deriving DecidableEq, Repr

instance : Inhabited Exit := ⟨⟨[], ⟨none, [], []⟩, 0, false⟩⟩

/-- The steps by a relation out of the configurations `S`. -/
def exitsOf (N : NFA Label) (S : List Conf) : List Exit :=
  S.flatMap fun c => (N.trans c.1).filterMap fun t =>
    if t.1.rel.isSome then some ⟨c.2.1, t.1, t.2, c.2.2⟩ else none

/-- The relations' letters into `s`, with the states they come from. -/
def entries (N : NFA Label) (s : Nat) : List (Nat × Label) :=
  (List.range N.size).flatMap fun q => (N.trans q).filterMap fun t =>
    if t.2 == s && t.1.rel.isSome then some (q, t.1) else none

/-- A letter of a relation within the builtin `r`, without checks. -/
def within (θ : Theory) (l : Label) (r : Builtin.Rel) : Bool :=
  match l.rel with
  | some rel => l.pre.isEmpty && l.post.isEmpty && θ.relIncl rel ⟨r.id, false⟩
  | none => false

/-- Kater's `canSkip`: a cycle that enters the event by `entry`, from `src`,
and leaves it by `ex`, in the same word, can do without the event: both
steps are within `po` (`po-loc`), and `N` reads a step that includes their
composition from `src` to where `ex` leads. -/
def canSkip (θ : Theory) (N : NFA Label) (src : Nat) (entry : Label) (ex : Exit) : Bool :=
  !ex.wraps && within θ entry .po && within θ ex.label .po &&
    (N.trans src).any fun t => t.2 == ex.dest && θ.labelIncl
      (Exp.bareLabel (if within θ entry .po_loc && within θ ex.label .po_loc
        then Builtin.Rel.po_loc.id else Builtin.Rel.po.id)) t.1

/-- Kater's `isEco`: a letter of a relation within `rf`, `mo` or `fr`. -/
def isEco (θ : Theory) (l : Label) : Bool :=
  match l.rel with
  | some r => θ.relIncl r ⟨Builtin.Rel.rf.id, false⟩ || θ.relIncl r ⟨Builtin.Rel.mo.id, false⟩ ||
      θ.relIncl r ⟨Builtin.Rel.fr.id, false⟩
  | none => false

/-- The exits out of the configurations `S` of state `s` that the check
asks about (Kater's `exitsToCheck`). -/
def toCheck (θ : Theory) (N : NFA Label) (s : Nat) (S : List Conf) : List Exit :=
  (exitsOf N S).filter fun ex =>
    !isEco θ ex.label && !θ.unsat (Guarded.union ex.preds addable) &&
      !(entries N s).all fun e => canSkip θ N e.1 e.2 ex

/-- The exits of `s` the check asks about, if the search for its
configurations checks. -/
def stateExits (θ : Theory) (N : NFA Label) (s : Nat) : Option (List Exit) :=
  let S := reach θ N (s, [], false)
  if closed θ N S && S.contains (s, [], false) then some (toCheck θ N s S) else none

/-- The exits of every state the check asks about. -/
def allExits (θ : Theory) (N : NFA Label) : Option (List Exit) :=
  ((List.range N.size).mapM (stateExits θ N)).map List.flatten

/-- Kater's `toEndOfWord`: the words from the event of each exit to the end of
the word it leaves the event in, read from a new starting state: the
exit's checks, with `addable`, its letter, and then `N` from where it
leads. -/
def words (N : NFA Label) (exits : List Exit) : NFA Label :=
  NFA.ofList (N.size + 1 + exits.length)
    (((List.range N.size).flatMap fun q => (N.trans q).map fun t => (q, t.1, t.2)) ++
      ((List.range exits.length).map fun i =>
        (N.size, ⟨none, Guarded.union exits[i]!.preds addable, []⟩, N.size + 1 + i)) ++
      ((List.range exits.length).map fun i => (N.size + 1 + i, exits[i]!.label, exits[i]!.dest)))
    [N.size] ((List.range N.size).filter N.isAccepting)

/-- The states of `N` are those of its arrays: its transitions and starting
states are of states, and each state accepts or not. -/
def closedStates (N : NFA Label) : Bool :=
  N.accepting.size == N.size && N.start.all (· < N.size) && N.outs.all (·.all (·.2 < N.size))

/-- The states the predicates' letters reach from the starting states: a
search, with fuel. -/
def predReach (N : NFA Label) (fuel : Nat := 100000) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut work : List Nat := N.start
  for _ in [0:fuel] do
    match work with
    | [] => break
    | q :: rest =>
      work := rest
      if seen.contains q then continue
      seen := seen.insert q
      work := ((N.trans q).filter (·.1.rel.isNone)).map (·.2) ++ work
  return seen.toList

/-- Whether `N` accepts no word of predicates alone (Kater's
`acceptsPredicatesOnly`): the states `predReach` found include the starting
ones, are closed under the predicates' letters, and accept nowhere. -/
def noPredWords (N : NFA Label) : Bool :=
  let R := predReach N
  N.start.all R.contains && R.all fun q =>
    !N.isAccepting q && (N.trans q).all fun t => t.1.rel.isSome || R.contains t.2

/-- `N` without the letters of relations within `lin`, which GenMC adds to
complete graphs only (`decideExtensibility`). -/
def dropLin (θ : Theory) (N : NFA Label) : NFA Label :=
  { N with outs := N.outs.map (·.filter fun t => match t.1.rel with
      | some r => !θ.relIncl r ⟨Builtin.Rel.lin.id, false⟩
      | none => true) }

/-- The predicates whose meaning at an event depends on events that may be
missing: the hazard pointers' protections, and `HEAP`. -/
def unstablePreds : List Int := [Builtin.Pred.HPPROT.id, Builtin.Pred.NOTHPPROT.id, Builtin.Pred.HEAP.id]

/-- A letter that keeps its meaning between two events when another event
goes: not of the predicates above, nor of `unprotected`. -/
def stableLabel (l : Label) : Bool :=
  (l.pre ++ l.post).all (fun p => !unstablePreds.contains p.id) &&
    match l.rel with
    | some r => r.id != Builtin.Rel.unprotected.id
    | none => true

/-- The words automata Lean builds, within Kater's, as the check splits
them: all, or for coherence those of the exits within their word and those
of the exits that go on into the next. -/
def wordsOk (θ : Theory) (N : NFA Label) (exits : List Exit) (single : Bool) :
    List WordsInclusion → Bool
  | [w] => !single && Guarded.prove θ (words N exits) w.words.nfa false (some w.words.origins)
  | [w₁, w₂] => single &&
    Guarded.prove θ (words N (exits.filter (!·.wraps))) w₁.words.nfa false (some w₁.words.origins) &&
    Guarded.prove θ (words N (exits.filter (·.wraps))) w₂.words.nfa false (some w₂.words.origins)
  | _ => false

/-- How the words came from the constraint: its automaton, as Kater read
its cycles, takes in Lean's automaton of the constraint without `lin`, and
denotes no more than it; it accepts no word of predicates alone, and its
letters keep their meaning when an event goes; and the words Lean builds
of it are within Kater's. -/
def checkCycles (x : Extensibility) : Except String Unit :=
  let θ := Theory.ofDecls x.module.decls
  let N := x.cycles
  if !x.re.wellFormed then .error "a let rec of the constraint is not left-linear"
  else if !closedStates N then .error "the constraint's automaton has transitions to no state"
  else if !N.outs.all (·.all fun t => stableLabel t.1) then
    .error "a letter of the constraint's automaton reads the hazard pointers' predicates or HEAP"
  else if !Guarded.prove θ (dropLin θ (Thompson.nfa x.re)) N false then
    .error "the constraint, without lin, is not within its automaton"
  else if !Guarded.prove θ N (Thompson.nfa x.re) false then
    .error "the constraint's automaton is not within the constraint"
  else if !noPredWords N then .error "the constraint's automaton accepts a word of predicates alone"
  else match allExits θ N with
    | none => .error "the search for the exits does not check"
    | some exits =>
      if wordsOk θ N exits x.single x.words then .ok ()
      else .error "Lean's words are not within Kater's"

/-! ## Soundness of the inclusions -/

variable {E : Type} {θ : Theory} {M : Interp E} {loc : Rel E}

local notation "⟦" A "⟧" => NFA.denote (Label.denote M) A

/-- **The words denote no more than the right-hand side**, if their
inclusion checks, the theory is sound, `po` is transitive, `any` relates
every two events and the assumptions hold. -/
theorem checkWords_sound (hθ : θ.Sound M loc) (hF : Facts M) {hyps : List Constraint}
    (hh : ∀ c ∈ hyps, c.Holds M) {w : WordsInclusion} (h : checkWords θ hyps w = .ok ()) :
    Rel.Sub ⟦w.words.nfa⟧ (w.rhs.denote M) := by
  unfold checkWords at h
  split at h
  · simp at h
  · rename_i hw
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hw
    split at h
    · simp at h
    · rename_i hs
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hs
      split at h
      · simp at h
      · rename_i R rot hR
        split at h
        · simp at h
        · rename_i hrot
          simp only [Bool.not_eq_true] at hrot
          obtain ⟨hRsub, -⟩ := Whole.right_sound hθ hF hh hR
          have hfin := Whole.final_sound hθ h
          intro a b hab
          exact Thompson.nfa_sound M w.rhs (Guarded.prove_sound hθ hs a b
            (hRsub hrot a b (hfin a b (Guarded.prove_sound hθ hw a b hab))))

theorem mem_altList_denote : ∀ (e : Exp) {a b : E},
    e.denote M a b ↔ ∃ f ∈ altList e, f.denote M a b
  | .alt l r, a, b => by
    simp only [altList, Exp.denote, Rel.union, List.mem_append]
    rw [mem_altList_denote l, mem_altList_denote r]
    constructor
    · rintro (⟨f, hf, h⟩ | ⟨f, hf, h⟩)
      · exact ⟨f, .inl hf, h⟩
      · exact ⟨f, .inr hf, h⟩
    · rintro ⟨f, hf | hf, h⟩
      · exact .inl ⟨f, hf, h⟩
      · exact .inr ⟨f, hf, h⟩
  | .label _, _, _ => by simp [altList]
  | .zero, _, _ => by simp [altList]
  | .seq _ _, _, _ => by simp [altList]
  | .star _, _, _ => by simp [altList]
  | .plus _, _, _ => by simp [altList]
  | .opt _, _, _ => by simp [altList]
  | .ref _, _, _ => by simp [altList]
  | .fix _ _, _, _ => by simp [altList]
  | .inv _, _, _ => by simp [altList]

/-- An expression of the same alternatives denotes the same. -/
theorem sameAlts_denote {a c : Exp} (h₁ : ∀ f ∈ altList a, f ∈ altList c)
    (h₂ : ∀ f ∈ altList c, f ∈ altList a) {x y : E} : a.denote M x y ↔ c.denote M x y := by
  rw [mem_altList_denote a, mem_altList_denote c]
  exact ⟨fun ⟨f, hf, h⟩ => ⟨f, h₁ f hf, h⟩, fun ⟨f, hf, h⟩ => ⟨f, h₂ f hf, h⟩⟩

/-- The `pporf` of an accepted check is `(ppo | rfe | tc | tj | lin)+`. -/
theorem pporfOk_denote {ppo pporf : Exp} (h : pporfOk ppo pporf = true) {x y : E} :
    pporf.denote M x y ↔ (pporfOf ppo).denote M x y := by
  unfold pporfOk at h
  split at h
  · rename_i a
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
    obtain ⟨h₁, h₂⟩ := h
    have hsame : ∀ {u v : E}, a.denote M u v ↔
        (Exp.alt (.alt (.alt (.alt ppo (bare .rfe)) (bare .tc)) (bare .tj)) (bare .lin)).denote M u v := by
      intro u v
      apply sameAlts_denote
      · intro f hf
        have := h₁ f hf
        simpa [altList, List.mem_append, or_assoc] using this
      · intro f hf
        apply h₂ f
        simpa [altList, List.mem_append, or_assoc] using hf
    simp only [pporfOf, Exp.denote, Rel.Plus, Rel.comp]
    constructor
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, hsame.mp h₁, Rel.Star.mono (fun _ _ => hsame.mp) _ _ h₂⟩
    · rintro ⟨z, h₁, h₂⟩
      exact ⟨z, hsame.mpr h₁, Rel.Star.mono (fun _ _ => hsame.mpr) _ _ h₂⟩
  · simp at h

theorem checkInclusions_go_sound {x : Extensibility}
    (hθ : (Theory.ofDecls x.module.decls).Sound M loc)
    (hF : Facts M) (hh : ∀ c ∈ Whole.hypsOf x.module.assumptions, c.Holds M) :
    ∀ {ws : List WordsInclusion}, checkInclusions.go x ws = .ok () →
      ∀ w ∈ ws, Rel.Sub ⟦w.words.nfa⟧ ((rhsOf x.pporf w.backToEvent).denote M)
  | [], _, w, hw => by simp at hw
  | w :: ws, h, w', hw' => by
    unfold checkInclusions.go at h
    split at h
    · simp at h
    · rename_i hrhs
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hrhs
      split at h
      · simp at h
      · rename_i hw
        rcases List.mem_cons.mp hw' with rfl | hw''
        · rw [← hrhs]
          exact checkWords_sound hθ hF hh hw
        · exact checkInclusions_go_sound hθ hF hh h w' hw''

/-- **The words of an accepted check denote no more than their right-hand
side**: `pporf ; any*`, or with `backToEvent` also `po+ ; (rf | mo |
fr)+`, wherever the module's theory is sound, `po` is transitive, `any`
relates every two events and the module's assumptions hold. -/
theorem checkInclusions_sound {x : Extensibility} (h : checkInclusions x = .ok ())
    (hθ : (Theory.ofDecls x.module.decls).Sound M loc) (hF : Facts M)
    (hh : Whole.HypsHold M x.module.assumptions) :
    ∀ w ∈ x.words, Rel.Sub ⟦w.words.nfa⟧ ((rhsOf x.pporf w.backToEvent).denote M) := by
  unfold checkInclusions at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · exact checkInclusions_go_sound hθ hF (Whole.hypsOf_hold hh) h

end Extensible

end KaterCert
