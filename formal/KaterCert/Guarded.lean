import Std.Data.HashMap
import KaterCert.NFA
import KaterCert.Theory

/-!
# Inclusion between automata, modulo normal forms

Kater's passes before the final inclusion check (`normalize`, the similarity
reductions, `to_DFA`, and the normalizations after each saturation) keep
what an automaton denotes, but not its words: they merge consecutive
predicates into one letter or into a relation's checks, add the domains and
codomains of relations to letters, and drop words whose predicates no event
satisfies together. So the automaton Kater compares is not letter by letter
the one an expression denotes, and the final check's certificates say
nothing of it.

This compares two automata `X` and `Y` as relations. A word is read as tests
and steps: a letter `[pre];r;[post]` tests `pre`, steps by `r`, and tests
`post`; consecutive tests are of one event, so their order does not matter.
`X` is within `Y` if, for each word of `X`, `Y` has a word with the same
number of steps, each within the step of `X` (`Theory.relIncl`), and tests of
each event that `X`'s tests of it entail, with what the theory says of the
steps around it (their domains and codomains). A word of `X` whose tests of
one event no event satisfies (`Theory.unsat`) needs no match.

`search` explores the configurations of `X` and `Y` that reading a word
reaches, without any proof, and `check` verifies what it found: that the
configurations start where both automata do, are closed under the steps of
`X`, and accept where `X` does. `check_sound` proves that this gives the
inclusion; `check_sound_cycle`, for cycles (`A & id`), that each cycle of `X`
is one of `Y`, where the tests of the event a cycle starts at may come from
either end of the word.
-/

namespace KaterCert

universe u

instance : Hashable Predicate := ⟨fun p => mixHash (hash p.id) (hash p.complement)⟩

namespace Guarded

/-! ## Predicate lists -/

/-- Predicates in Kater's order: by id, the plain one first. -/
def Predicate.lt (p q : Predicate) : Bool :=
  p.id < q.id || (p.id == q.id && !p.complement && q.complement)

/-- Adds a predicate to a sorted list of predicates. -/
def insertPred (p : Predicate) : List Predicate → List Predicate
  | [] => [p]
  | q :: qs => if p == q then q :: qs else if Predicate.lt p q then p :: q :: qs
    else q :: insertPred p qs

/-- The union of two lists of predicates, sorted if the first one is. -/
def union (ps qs : List Predicate) : List Predicate := qs.foldl (fun acc q => insertPred q acc) ps

theorem mem_insertPred {p a : Predicate} : ∀ {qs : List Predicate}, a ∈ insertPred p qs → a = p ∨ a ∈ qs
  | [], h => by simp [insertPred] at h; exact .inl h
  | q :: qs, h => by
    unfold insertPred at h
    split at h
    · exact .inr h
    · split at h
      · simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inl h
        · exact .inr h
      · simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · exact .inr (.inl h)
        · rcases mem_insertPred h with h | h
          · exact .inl h
          · exact .inr (.inr h)

theorem mem_union {a : Predicate} : ∀ {ps qs : List Predicate}, a ∈ union ps qs → a ∈ ps ∨ a ∈ qs
  | ps, [], h => .inl h
  | ps, q :: qs, h => by
    simp only [union, List.foldl_cons] at h
    rcases mem_union (ps := insertPred q ps) (qs := qs) h with h | h
    · rcases mem_insertPred h with rfl | h
      · exact .inr (List.mem_cons_self ..)
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

variable {E : Type u} {M : Interp E}

theorem checks_union {ps qs : List Predicate} {e : E} (hp : Checks M ps e) (hq : Checks M qs e) :
    Checks M (union ps qs) e := by
  intro a ha
  rcases mem_union ha with h | h
  · exact hp a h
  · exact hq a h

/-- `T'` is part of `T`. -/
def subTests (T' T : List Predicate) : Bool := T'.all fun p => T.contains p

theorem checks_of_subTests {T' T : List Predicate} (h : subTests T' T = true) {e : E}
    (hT : Checks M T e) : Checks M T' e := by
  intro p hp
  simp only [subTests, List.all_eq_true, List.contains_iff_mem] at h
  exact hT p (h p hp)

/-! ## Configurations -/

/-- A configuration of `Y`: a state, and the tests it read since its last
step, of the event `X` is at, which `X`'s tests of it have to entail. -/
abbrev RConf := Nat × List Predicate

/-- A configuration of the search: a state of `X`, the tests `X` read since
its last step (of the current event), for cycles the tests of the event the
cycle starts at once `X` stepped away from it, and the configurations of `Y`
that may match. -/
structure Macro where
  x : Nat
  tests : List Predicate
  base : Option (List Predicate)
  right : List RConf
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Lists of predicates in lexicographic order. -/
def listLe : List Predicate → List Predicate → Bool
  | [], _ => true
  | _ :: _, [] => false
  | p :: ps, q :: qs => Predicate.lt p q || (p == q && listLe ps qs)

/-- Configurations in a canonical order, without duplicates. -/
def canon (S : List RConf) : List RConf :=
  (S.mergeSort fun a b => a.1 < b.1 || (a.1 == b.1 && listLe a.2 b.2)).eraseDups

/-! The certificate's configurations need no canonical form for the proof:
only that each comes from a step. `canon` keeps the search finite. -/

theorem mem_canon {c : RConf} {S : List RConf} (h : c ∈ canon S) : c ∈ S := by
  unfold canon at h
  have h' : c ∈ (S.mergeSort _) := List.mem_eraseDups.mp h
  exact List.mem_mergeSort.mp h'

/-! ## The right automaton's predicate steps -/

/-- `PStep θ Y K y y'`: `Y` goes from `y` to `y'` by predicate steps whose
checks `K` entails. -/
inductive PStep (θ : Theory) (Y : NFA Label) (K : List Predicate) : Nat → Nat → Prop
  | refl (y : Nat) : PStep θ Y K y y
  | step {y : Nat} {l : Label} {y' y'' : Nat} : (l, y') ∈ Y.trans y → l.rel = none →
      θ.entails K l.pre = true → PStep θ Y K y' y'' → PStep θ Y K y y''

theorem PStep.snoc {θ : Theory} {Y : NFA Label} {K : List Predicate} {y y' y'' : Nat}
    {l : Label} (h : PStep θ Y K y y') (ht : (l, y'') ∈ Y.trans y') (hl : l.rel = none)
    (hK : θ.entails K l.pre = true) : PStep θ Y K y y'' := by
  induction h with
  | refl => exact .step ht hl hK (.refl _)
  | step h₁ h₂ h₃ _ ih => exact .step h₁ h₂ h₃ (ih ht)

/-- One step of the closure: the unmarked states `Y` reaches from `y` by one
predicate step whose checks `K` entails, added to the frontier and to the
result, and marked. -/
def closureStep (θ : Theory) (K : List Predicate) :
    List (Label × Nat) → List Nat → Array Bool → List Nat → List Nat × Array Bool × List Nat
  | [], fr, m, acc => (fr, m, acc)
  | (l, y') :: ts, fr, m, acc =>
    if l.rel.isNone && θ.entails K l.pre && !(m.getD y' false) then
      closureStep θ K ts (y' :: fr) (m.setIfInBounds y' true) (y' :: acc)
    else closureStep θ K ts fr m acc

/-- The closure, a frontier at a time, with `fuel` steps at most. -/
def closureGo (θ : Theory) (Y : NFA Label) (K : List Predicate) :
    Nat → List Nat → Array Bool → List Nat → List Nat
  | 0, _, _, acc => acc
  | _ + 1, [], _, acc => acc
  | fuel + 1, y :: fr, m, acc =>
    let r := closureStep θ K (Y.trans y) fr m acc
    closureGo θ Y K fuel r.1 r.2.1 r.2.2

/-- How many steps the closure may take: one per state and transition of
`Y`, which marking the states it visits makes enough. -/
def fuel (Y : NFA Label) : Nat := Y.outs.foldl (fun n ts => n + ts.length + 1) 1

/-- The states of `Y` that the configurations `S` whose tests `K` entails
reach by predicate steps whose checks `K` entails. -/
def closure (θ : Theory) (Y : NFA Label) (K : List Predicate) (S : List RConf) : List Nat :=
  let init := (S.filter fun c => θ.entails K c.2).map (·.1)
  let marks := init.foldl (fun m y => m.setIfInBounds y true) (Array.replicate Y.size false)
  closureGo θ Y K (fuel Y) init marks init

/-- What `Y` steps to from the configurations `S`, by a step within `r` from
an event whose tests `K` are: the destinations, with the checks of the step's
end, which the next event's tests have to entail. The checks of the step's
start may also follow from the domain of `Y`'s relation, which the step is
in. -/
def next (θ : Theory) (Y : NFA Label) (K : List Predicate) (r : Relation) (S : List RConf) :
    List RConf :=
  (closure θ Y K S).flatMap fun y' => (Y.trans y').filterMap fun t =>
    match t.1.rel with
    | some s => if θ.entails (K ++ θ.dom s) t.1.pre && θ.relIncl r s then some (t.2, t.1.post)
      else none
    | none => none

/-! ## The steps of the search -/

/-- The configurations a step of `X` out of `m` leads to, but those whose
tests no event satisfies. In cycles (`cycle`), the tests of the event the
word starts at are kept once `X` steps away from it. -/
def steps (θ : Theory) (X Y : NFA Label) (cycle : Bool) (m : Macro) : List Macro :=
  (X.trans m.x).filterMap fun t =>
    match t.1.rel with
    | none =>
      let T := union m.tests t.1.pre
      if θ.unsat T then none else some { m with x := t.2, tests := T }
    | some r =>
      let K := union (union m.tests t.1.pre) (θ.dom r)
      let T := union t.1.post (θ.codom r)
      if θ.unsat K || θ.unsat T then none
      else some {
        x := t.2
        tests := T
        base := if cycle then (m.base <|> some K) else none
        right := canon (next θ Y K r m.right) }

/-- What `X` and `Y` know of the event a word of `X` ends at, from `m`. -/
def final (cycle : Bool) (m : Macro) : List Predicate :=
  if cycle then union m.tests (m.base.getD []) else m.tests

/-- Where `X` accepts, so does a configuration of `Y`, unless no event
satisfies `X`'s tests. -/
def acceptOk (θ : Theory) (X Y : NFA Label) (cycle : Bool) (m : Macro) : Bool :=
  !X.isAccepting m.x || θ.unsat (final cycle m) ||
    (closure θ Y (final cycle m) m.right).any Y.isAccepting

/-- `m'` makes a stronger claim than `s`: of the same state of `X`, with
fewer tests, the same base, and configurations of `Y` each with more tests
than one of `s`. -/
def covers (m' s : Macro) : Bool :=
  m'.x == s.x && subTests m'.tests s.tests &&
    (match m'.base, s.base with
      | none, none => true
      | some K', some K => subTests K' K
      | _, _ => false) &&
    m'.right.all fun c => s.right.any fun d => d.1 == c.1 && subTests d.2 c.2

/-- A certificate: the configurations, and for each the indices of the
configurations that cover its steps, in the order `steps` lists them; and for
each start of `X`, the index of a configuration that covers it. -/
structure Cert where
  macros : Array Macro
  succ : Array (List Nat)
  start : List Nat
  deriving Inhabited

/-- Each of the configurations `ss` is covered by the one the index beside
it names. -/
def coveredBy (P : Array Macro) : List Macro → List Nat → Bool
  | [], [] => true
  | s :: ss, j :: js => (match P[j]? with | some m' => covers m' s | none => false) &&
    coveredBy P ss js
  | _, _ => false

/-- The configuration a word of `X` starts in at `x`. -/
def initial (Y : NFA Label) (x : Nat) : Macro :=
  { x, tests := [], base := none, right := canon (Y.start.map fun y => (y, [])) }

/-- Whether the certificate proves that `X` is within `Y` (`cycle`: that each
cycle of `X` is one of `Y`). -/
def check (θ : Theory) (X Y : NFA Label) (cycle : Bool) (c : Cert) : Bool :=
  c.macros.size == c.succ.size &&
    coveredBy c.macros (X.start.map (initial Y)) c.start &&
    (List.range c.macros.size).all fun i =>
      acceptOk θ X Y cycle (c.macros[i]?.getD default) &&
        coveredBy c.macros (steps θ X Y cycle (c.macros[i]?.getD default)) (c.succ[i]?.getD [])

/-! ## The search -/

instance : Hashable Relation := ⟨fun r => mixHash (hash r.id) (hash r.inverse)⟩
instance : Hashable Label := ⟨fun l => mixHash (hash l.rel) (mixHash (hash l.pre) (hash l.post))⟩

/-- Which states of `Y` simulate which, letter by letter: `y₂` simulates
`y₁` (entry `y₁ * n + y₂`) if it accepts where `y₁` does and follows each of
its steps with the same letter into a state that simulates the step's
destination. Only the search uses it, to drop configurations of `Y` that
others dominate; `check` verifies what is left. -/
def simulation (Y : NFA Label) : Array Bool := Id.run do
  let n := Y.size
  let mut ids : Std.HashMap Label Nat := {}
  for ts in Y.outs do
    for (l, _) in ts do
      if !ids.contains l then ids := ids.insert l ids.size
  let outs : Array (Array (Nat × Nat)) :=
    Y.outs.map fun ts => (ts.map fun (l, d) => (ids.getD l 0, d)).toArray
  let mut sim := Array.replicate (n * n) true
  for y₁ in [0:n] do
    for y₂ in [0:n] do
      if Y.isAccepting y₁ && !Y.isAccepting y₂ then sim := sim.set! (y₁ * n + y₂) false
  let mut changed := true
  while changed do
    changed := false
    for y₁ in [0:n] do
      for y₂ in [0:n] do
        if y₁ != y₂ && sim[y₁ * n + y₂]! then
          let ok := outs[y₁]!.all fun (l, d₁) => outs[y₂]!.any fun (l', d₂) =>
            l == l' && d₁ < n && d₂ < n && sim[d₁ * n + d₂]!
          if !ok then
            sim := sim.set! (y₁ * n + y₂) false
            changed := true
  return sim

/-- `S` without the configurations another of `S` dominates: a state that
simulates theirs, with fewer tests to come (of equal ones, the first
stays). -/
def reduce (sim : Array Bool) (n : Nat) (S : List RConf) : List RConf :=
  if S.length ≤ 1 then S else
  let arr := S.toArray
  (List.range arr.size).filterMap fun i =>
    let (y₁, U₁) := arr[i]!
    let dominated := (List.range arr.size).any fun j =>
      j != i &&
        (let (y₂, U₂) := arr[j]!
         y₁ < n && y₂ < n && sim.getD (y₁ * n + y₂) false && subTests U₂ U₁ &&
           (j < i || !(sim.getD (y₂ * n + y₁) false && subTests U₁ U₂)))
    if dominated then none else some arr[i]!

/-- Explores the configurations reachable from the starts of `X`,
breadth-first, at most `limit` of them; `none` if there are more. A step
lands on a configuration found before if one covers it, and drops the
configurations of `Y` that others dominate. Nothing about it is proved:
`check` verifies what it finds. -/
def search (θ : Theory) (X Y : NFA Label) (cycle : Bool) (limit : Nat := 1000000)
    (hint : Option (Array (List Nat)) := none) : Option Cert := Id.run do
  let sim := simulation Y
  let n := Y.size
  -- With a hint (the states of `Y` each state of `X` stands for), a step of
  -- `X` keeps the configurations of `Y` that reach one of them by predicate
  -- steps
  let back : Array (List Nat) := Id.run do
    let mut preds : Array (List Nat) := Array.replicate n []
    for y in [0:n] do
      for (l, d) in Y.trans y do
        if l.rel.isNone && d < n then preds := preds.modify d (y :: ·)
    let mut back := Array.replicate n []
    for o in [0:n] do
      let mut seen : Std.HashSet Nat := {}
      let mut work := [o]
      seen := seen.insert o
      for _ in [0:n + 1] do
        match work with
        | [] => break
        | y :: rest =>
          work := rest
          for p in preds[y]! do
            if !seen.contains p then
              seen := seen.insert p
              work := p :: work
      back := back.set! o seen.toList
    return back
  let allowed (x : Nat) : Option (Std.HashSet Nat) := hint.map fun h =>
    ((h.getD x []).flatMap fun o => back.getD o []).foldl (·.insert ·) {}
  let restrict (m : Macro) : Macro :=
    match allowed m.x with
    | some a => { m with right := m.right.filter fun c => a.contains c.1 }
    | none => m
  let mut index : Std.HashMap Macro Nat := {}
  let mut byX : Std.HashMap Nat (List Nat) := {}
  let mut macros : Array Macro := #[]
  let mut start : List Nat := []
  for x in X.start do
    let m := initial Y x
    match index.get? m with
    | some i => start := start ++ [i]
    | none =>
      index := index.insert m macros.size
      byX := byX.insert m.x (macros.size :: byX.getD m.x [])
      start := start ++ [macros.size]
      macros := macros.push m
  let mut succ : Array (List Nat) := #[]
  let mut i := 0
  while i < macros.size do
    if macros.size > limit then return none
    let m := macros[i]!
    let mut is : List Nat := []
    for s in steps θ X Y cycle m do
      match index.get? s with
      | some j => is := j :: is
      | none =>
        let r' := restrict s
        let r := { r' with right := reduce sim n r'.right }
        match index.get? r with
        | some j => is := j :: is
        | none =>
          match (byX.getD r.x []).find? fun j => covers macros[j]! s with
          | some j => is := j :: is
          | none =>
            index := index.insert r macros.size
            byX := byX.insert r.x (macros.size :: byX.getD r.x [])
            is := macros.size :: is
            macros := macros.push r
    succ := succ.push is.reverse
    i := i + 1
  return some { macros, succ, start }

/-- A search for configurations that each pair a state of `X` with one
configuration of `Y`: a simulation of `X` by `Y`, the greatest one among
the pairs a word reaches, if it covers the starts. Cheaper than `search`
where `Y` is far more nondeterministic than its matches need, as after a
saturation; `check` verifies what it finds as it does `search`'s. -/
def searchSingle (θ : Theory) (X Y : NFA Label) (cycle : Bool) (limit : Nat := 2000000) :
    Option Cert := Id.run do
  let single (m : Macro) (c : RConf) : Macro := { m with right := [c] }
  let mut index : Std.HashMap Macro Nat := {}
  let mut macros : Array Macro := #[]
  -- for each configuration, for each of its steps, the candidates covering it
  let mut cands : Array (List (List Nat)) := #[]
  let mut starts : List (List Nat) := []
  for x in X.start do
    let m := initial Y x
    let mut is := []
    for c in m.right do
      let m' := single m c
      match index.get? m' with
      | some j => is := j :: is
      | none =>
        index := index.insert m' macros.size
        is := macros.size :: is
        macros := macros.push m'
    starts := starts ++ [is]
  let mut i := 0
  while i < macros.size do
    if macros.size > limit then return none
    let m := macros[i]!
    let mut per : List (List Nat) := []
    for s in steps θ X Y cycle m do
      let mut is := []
      for c in s.right do
        let m' := single s c
        match index.get? m' with
        | some j => is := j :: is
        | none =>
          index := index.insert m' macros.size
          is := macros.size :: is
          macros := macros.push m'
      per := is :: per
    cands := cands.push per.reverse
    i := i + 1
  -- the greatest set of configurations that accept and whose steps each
  -- have a candidate in the set
  let mut alive := macros.map fun m => acceptOk θ X Y cycle m
  let mut changed := true
  while changed do
    changed := false
    for j in [0:macros.size] do
      if alive[j]! && !(cands[j]!.all fun is => is.any (alive[·]!)) then
        alive := alive.set! j false
        changed := true
  if !(starts.all fun is => is.any (alive[·]!)) then return none
  -- renumber the live ones
  let mut renum : Array Nat := Array.replicate macros.size 0
  let mut kept : Array Macro := #[]
  for j in [0:macros.size] do
    if alive[j]! then
      renum := renum.set! j kept.size
      kept := kept.push macros[j]!
  let pick (is : List Nat) : Nat := renum[(is.find? (alive[·]!)).getD 0]!
  let mut succ : Array (List Nat) := #[]
  for j in [0:macros.size] do
    if alive[j]! then succ := succ.push (cands[j]!.map pick)
  return some { macros := kept, succ, start := starts.map pick }

/-- Statistics of `search` up to `limit` configurations, for triage: how
many configurations per state of `X`, how many configurations of `Y` per
configuration, and how many distinct test sets. -/
def statsSearch (θ : Theory) (X Y : NFA Label) (cycle : Bool) (limit : Nat) : String := Id.run do
  let sim := simulation Y
  let n := Y.size
  let mut index : Std.HashMap Macro Nat := {}
  let mut byX : Std.HashMap Nat (List Nat) := {}
  let mut macros : Array Macro := #[]
  for x in X.start do
    let m := initial Y x
    if !index.contains m then
      index := index.insert m macros.size
      byX := byX.insert m.x (macros.size :: byX.getD m.x [])
      macros := macros.push m
  let mut i := 0
  while i < macros.size && macros.size ≤ limit do
    let m := macros[i]!
    for s in steps θ X Y cycle m do
      if !index.contains s then
        let r := { s with right := reduce sim n s.right }
        if !index.contains r && ((byX.getD r.x []).find? fun j => covers macros[j]! s).isNone then
          index := index.insert r macros.size
          byX := byX.insert r.x (macros.size :: byX.getD r.x [])
          macros := macros.push r
    i := i + 1
  let perX := byX.fold (fun acc _ is => max acc is.length) 0
  let rights := macros.foldl (fun acc m => max acc m.right.length) 0
  let avgRight := macros.foldl (fun acc m => acc + m.right.length) 0 / max macros.size 1
  let tests := (macros.map (·.tests)).toList.eraseDups.length
  let worst := byX.fold (fun acc x is => if is.length > acc.2 then (x, is.length) else acc) (0, 0)
  let sample := ((byX.getD worst.1 []).take 6).map fun j => (macros[j]!.tests.length, macros[j]!.right)
  return s!"{macros.size} configurations; at most {perX} per state of X; right sets up to {rights} (average {avgRight}); {tests} distinct test sets; state {worst.1}: {repr sample}"

/-- Whether `X` is within `Y` (`cycle`: each cycle of `X` one of `Y`), as far
as the search and the check can tell. -/
def prove (θ : Theory) (X Y : NFA Label) (cycle : Bool)
    (hint : Option (Array (List Nat)) := none) : Bool :=
  (match hint with
   | some _ => match search θ X Y cycle 1000000 hint with
     | some c => check θ X Y cycle c
     | none => false
   | none => false) ||
  match search θ X Y cycle with
  | some c => check θ X Y cycle c
  | none => false

/-! ## Soundness -/

section Closure

variable {θ : Theory} {Y : NFA Label} {K : List Predicate}

theorem closureStep_good {G : Nat → Prop}
    (hG : ∀ v l v', G v → (l, v') ∈ Y.trans v → l.rel = none → θ.entails K l.pre = true → G v')
    {y : Nat} (hy : G y) :
    ∀ {ts : List (Label × Nat)} {fr : List Nat} {m : Array Bool} {acc : List Nat},
      (∀ t ∈ ts, t ∈ Y.trans y) → (∀ v ∈ fr, G v) → (∀ v ∈ acc, G v) →
      (∀ v ∈ (closureStep θ K ts fr m acc).1, G v) ∧ (∀ v ∈ (closureStep θ K ts fr m acc).2.2, G v)
  | [], _, _, _, _, hfr, hacc => ⟨hfr, hacc⟩
  | (l, y') :: ts, fr, m, acc, hts, hfr, hacc => by
    unfold closureStep
    have hts' : ∀ t ∈ ts, t ∈ Y.trans y := fun t ht => hts t (List.mem_cons_of_mem _ ht)
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at hc
      have hy' : G y' := hG y l y' hy (hts _ (List.mem_cons_self ..)) hc.1.1 hc.1.2
      exact closureStep_good hG hy hts'
        (fun v hv => by
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hy'
          · exact hfr v hv)
        (fun v hv => by
          simp only [List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact hy'
          · exact hacc v hv)
    · exact closureStep_good hG hy hts' hfr hacc

theorem closureGo_good {G : Nat → Prop}
    (hG : ∀ v l v', G v → (l, v') ∈ Y.trans v → l.rel = none → θ.entails K l.pre = true → G v') :
    ∀ {fuel : Nat} {fr : List Nat} {m : Array Bool} {acc : List Nat},
      (∀ v ∈ fr, G v) → (∀ v ∈ acc, G v) → ∀ v ∈ closureGo θ Y K fuel fr m acc, G v
  | 0, _, _, _, _, hacc => by simpa [closureGo] using hacc
  | _ + 1, [], _, _, _, hacc => by simpa [closureGo] using hacc
  | fuel + 1, y :: fr, m, acc, hfr, hacc => by
    unfold closureGo
    have hy := hfr y (List.mem_cons_self ..)
    obtain ⟨h₁, h₂⟩ := closureStep_good (fr := fr) (m := m) (acc := acc) hG hy
      (fun _ ht => ht) (fun v hv => hfr v (List.mem_cons_of_mem _ hv)) hacc
    exact closureGo_good hG h₁ h₂

/-- Each state of the closure is reached from a configuration whose tests
`K` entails, by predicate steps whose checks `K` entails. -/
theorem mem_closure {S : List RConf} {y' : Nat} (h : y' ∈ closure θ Y K S) :
    ∃ c ∈ S, θ.entails K c.2 = true ∧ PStep θ Y K c.1 y' := by
  let G : Nat → Prop := fun v => ∃ c ∈ S, θ.entails K c.2 = true ∧ PStep θ Y K c.1 v
  have hG : ∀ v l v', G v → (l, v') ∈ Y.trans v → l.rel = none → θ.entails K l.pre = true →
      G v' := by
    rintro v l v' ⟨c, hc, hK, hp⟩ ht hl hl'
    exact ⟨c, hc, hK, hp.snoc ht hl hl'⟩
  have hinit : ∀ v ∈ (S.filter fun c => θ.entails K c.2).map (·.1), G v := by
    intro v hv
    simp only [List.mem_map, List.mem_filter] at hv
    obtain ⟨c, ⟨hc, hK⟩, rfl⟩ := hv
    exact ⟨c, hc, hK, .refl _⟩
  exact closureGo_good hG hinit hinit y' h

variable {E : Type u} {M : Interp E} {loc : Rel E}

/-- Predicate steps that the tests of an event entail read that event
alone: prepended to a word, they leave its relation. -/
theorem PStep.lift (hθ : θ.Sound M loc) {c b : E} (hK : Checks M K c) {y y' : Nat}
    (h : PStep θ Y K y y') {w : List Label} (hw : Y.Accepts y' w)
    (hr : wordRel (Label.denote M) w c b) :
    ∃ w', Y.Accepts y w' ∧ wordRel (Label.denote M) w' c b := by
  induction h generalizing w with
  | refl => exact ⟨w, hw, hr⟩
  | @step y l y₁ y₂ ht hl hl' _ ih =>
    obtain ⟨w', hw', hr'⟩ := ih hw hr
    refine ⟨l :: w', .cons ht hw', c, ?_, hr'⟩
    simp only [Label.denote, hl, true_and]
    exact hθ.entails hl' hK

theorem mem_next {r : Relation} {S : List RConf} {c : RConf} (h : c ∈ next θ Y K r S) :
    ∃ y' ∈ closure θ Y K S, ∃ l s, (l, c.1) ∈ Y.trans y' ∧ l.rel = some s ∧
      θ.entails (K ++ θ.dom s) l.pre = true ∧ θ.relIncl r s = true ∧ c.2 = l.post := by
  simp only [next, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨y', hy', ⟨l, d⟩, ht, hf⟩ := h
  simp only at hf
  split at hf
  · rename_i s hs
    split at hf
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      simp only [Option.some.injEq] at hf
      subst hf
      exact ⟨y', hy', l, s, ht, hs, hc.1, hc.2, rfl⟩
    · simp at hf
  · simp at hf

end Closure

theorem coveredBy_spec {P : Array Macro} :
    ∀ {ss : List Macro} {js : List Nat}, coveredBy P ss js = true →
      ∀ s ∈ ss, ∃ (j : Nat) (m' : Macro), P[j]? = some m' ∧ covers m' s = true
  | [], [], _ => by simp
  | s :: ss, j :: js, h => by
    simp only [coveredBy, Bool.and_eq_true] at h
    intro s' hs'
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · split at h
      · rename_i m' hm'
        exact ⟨j, m', hm', h.1⟩
      · simp at h
    · exact coveredBy_spec h.2 s' hs'
  | [], _ :: _, h => by simp [coveredBy] at h
  | _ :: _, [], h => by simp [coveredBy] at h

section Claim

variable {E : Type u} (θ : Theory) (X Y : NFA Label) (cycle : Bool) (M : Interp E)

/-- What a configuration claims: for each word of `X` from its state,
reading from an event its tests hold of, `Y` reads the same from one of its
configurations whose tests hold. For cycles, of words back to the event the
cycle starts at, `a`, whose tests the base holds, if `X` stepped away from
it. -/
def Claim (w : List Label) (m : Macro) : Prop :=
  ∀ (a c b : E), X.Accepts m.x w → Checks M m.tests c →
    (cycle = true → (m.base = none → c = a) ∧ (∀ K0, m.base = some K0 → Checks M K0 a) ∧ b = a) →
    wordRel (Label.denote M) w c b →
    ∃ y U, (y, U) ∈ m.right ∧ Checks M U c ∧
      ∃ w', Y.Accepts y w' ∧ wordRel (Label.denote M) w' c b

variable {θ X Y cycle M}

theorem covers_claim {w : List Label} {m' s : Macro} (hc : covers m' s = true)
    (h : Claim X Y cycle M w m') : Claim X Y cycle M w s := by
  intro a c b hw hT hbase hr
  simp only [covers, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true] at hc
  obtain ⟨⟨⟨hx, hsub⟩, hb⟩, hright⟩ := hc
  rw [← hx] at hw
  have hbase' : cycle = true → (m'.base = none → c = a) ∧
      (∀ K0, m'.base = some K0 → Checks M K0 a) ∧ b = a := by
    intro hcy
    obtain ⟨h₁, h₂, h₃⟩ := hbase hcy
    refine ⟨fun hn => ?_, fun K0 hK0 => ?_, h₃⟩
    · rw [hn] at hb
      split at hb <;> simp_all
    · rw [hK0] at hb
      split at hb
      · simp at *
      · rename_i K' K hK' hK
        cases hK'
        exact checks_of_subTests hb (h₂ K hK)
      · simp at hb
  obtain ⟨y, U', hyU, hU', w', hw', hr'⟩ := h a c b hw (checks_of_subTests hsub hT) hbase' hr
  obtain ⟨d, hd, hdy, hdU⟩ := hright (y, U') hyU
  refine ⟨d.1, d.2, ?_, checks_of_subTests hdU hU', w', ?_, hr'⟩
  · simpa using hd
  · simp only at hdy
    rw [hdy]
    exact hw'

variable {loc : Rel E}

theorem check_spec {c : Cert} (h : check θ X Y cycle c = true) :
    coveredBy c.macros (X.start.map (initial Y)) c.start = true ∧
      ∀ (i : Nat) (m : Macro), c.macros[i]? = some m →
        acceptOk θ X Y cycle m = true ∧
          coveredBy c.macros (steps θ X Y cycle m) (c.succ[i]?.getD []) = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, hstart⟩, hall⟩ := h
  refine ⟨hstart, fun i m hm => ?_⟩
  have hi : i < c.macros.size := by
    rcases Nat.lt_or_ge i c.macros.size with hi | hi
    · exact hi
    · simp [Array.getElem?_eq_none hi] at hm
  have := hall i hi
  rw [hm] at this
  exact this

/-- Each configuration of an accepted certificate claims what it does. -/
theorem claim_all (hθ : θ.Sound M loc) {c : Cert} (h : check θ X Y cycle c = true) :
    ∀ (w : List Label) (i : Nat) (m : Macro), c.macros[i]? = some m → Claim X Y cycle M w m := by
  obtain ⟨-, hm⟩ := check_spec h
  intro w
  induction w with
  | nil =>
    intro i m hi a e b hw hT hbase hr
    have hacc : X.isAccepting m.x = true := by cases hw with | nil h => exact h
    have heb : e = b := hr
    subst heb
    have hfinal : Checks M (final cycle m) e := by
      unfold final
      split
      · rename_i hcy
        obtain ⟨-, h₂, h₃⟩ := hbase hcy
        subst h₃
        refine checks_union hT ?_
        cases hb : m.base with
        | none => intro p hp; simp at hp
        | some K0 => simpa using h₂ K0 hb
      · exact hT
    have hok := (hm i m hi).1
    simp only [acceptOk, hacc, Bool.not_true, Bool.false_or, Bool.or_eq_true,
      List.any_eq_true] at hok
    rcases hok with hun | ⟨y', hy', hy'acc⟩
    · exact absurd hfinal (hθ.unsat _ hun e)
    · obtain ⟨⟨y, U⟩, hyU, hK, hp⟩ := mem_closure hy'
      obtain ⟨w', hw', hr'⟩ := hp.lift hθ hfinal (.nil hy'acc) (show wordRel _ [] e e from rfl)
      exact ⟨y, U, hyU, hθ.entails hK hfinal, w', hw', hr'⟩
  | cons l w ih =>
    intro i m hi a e b hw hT hbase hr
    obtain ⟨-, hcov⟩ := hm i m hi
    have hcov := coveredBy_spec hcov
    cases hw with
    | @cons _ _ x' _ ht hw' =>
      obtain ⟨d, hl, hr'⟩ := hr
      cases hrel : l.rel with
      | none =>
        simp only [Label.denote, hrel] at hl
        obtain ⟨rfl, hpre⟩ := hl
        have hT' : Checks M (union m.tests l.pre) e := checks_union hT hpre
        have hun : θ.unsat (union m.tests l.pre) = false := by
          cases hu : θ.unsat (union m.tests l.pre)
          · rfl
          · exact absurd hT' (hθ.unsat _ hu e)
        have hs : { m with x := x', tests := union m.tests l.pre } ∈ steps θ X Y cycle m := by
          simp only [steps, List.mem_filterMap]
          exact ⟨(l, x'), ht, by simp [hrel, hun]⟩
        obtain ⟨j, m'', hj, hc⟩ := hcov _ hs
        exact covers_claim hc (ih j m'' hj) a e b hw' hT' hbase hr'
      | some r =>
        simp only [Label.denote, hrel] at hl
        obtain ⟨hpre, hrd, hpost⟩ := hl
        let K := union (union m.tests l.pre) (θ.dom r)
        have hK : Checks M K e :=
          checks_union (checks_union hT hpre) (fun p hp => hθ.dom r p hp e d hrd)
        have hT' : Checks M (union l.post (θ.codom r)) d :=
          checks_union hpost (fun p hp => hθ.codom r p hp e d hrd)
        have hun : (θ.unsat K || θ.unsat (union l.post (θ.codom r))) = false := by
          cases hu : θ.unsat K
          · cases hu' : θ.unsat (union l.post (θ.codom r))
            · rfl
            · exact absurd hT' (hθ.unsat _ hu' d)
          · exact absurd hK (hθ.unsat _ hu e)
        let s : Macro := {
          x := x'
          tests := union l.post (θ.codom r)
          base := if cycle then (m.base <|> some K) else none
          right := canon (next θ Y K r m.right) }
        have hs : s ∈ steps θ X Y cycle m := by
          have hun' : (θ.unsat (union (union m.tests l.pre) (θ.dom r)) ||
              θ.unsat (union l.post (θ.codom r))) = false := hun
          simp only [steps, List.mem_filterMap]
          refine ⟨(l, x'), ht, ?_⟩
          simp only [hrel, hun', Bool.false_eq_true, ite_false]
          rfl
        obtain ⟨j, m'', hj, hc⟩ := hcov _ hs
        have hbase' : cycle = true → (s.base = none → d = a) ∧
            (∀ K0, s.base = some K0 → Checks M K0 a) ∧ b = a := by
          intro hcy
          obtain ⟨h₁, h₂, h₃⟩ := hbase hcy
          refine ⟨fun hn => ?_, fun K0 hK0 => ?_, h₃⟩
          · simp only [s, hcy, ite_true] at hn
            cases hmb : m.base <;>
              simp [hmb, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hn
          · simp only [s, hcy, ite_true] at hK0
            cases hmb : m.base with
            | none =>
              simp only [hmb, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
                Option.some.injEq] at hK0
              rw [← h₁ hmb, ← hK0]
              exact hK
            | some K1 =>
              simp only [hmb, HOrElse.hOrElse, OrElse.orElse, Option.orElse,
                Option.some.injEq] at hK0
              rw [← hK0]
              exact h₂ K1 hmb
        obtain ⟨y'', U'', hyU'', hU'', w'', hw'', hr''⟩ :=
          covers_claim hc (ih j m'' hj) a d b hw' hT' hbase' hr'
        obtain ⟨y', hy', l', s', ht', hrel', hpre', hincl, hU⟩ := mem_next (mem_canon hyU'')
        obtain ⟨⟨y, U⟩, hyU, hKU, hp⟩ := mem_closure hy'
        have hsd : s'.denote M e d := hθ.relIncl r s' hincl e d hrd
        have hl' : Label.denote M l' e d := by
          simp only [Label.denote, hrel']
          refine ⟨hθ.entails hpre' (fun p hp => ?_), hsd, ?_⟩
          · simp only [List.mem_append] at hp
            rcases hp with hp | hp
            · exact hK p hp
            · exact hθ.dom s' p hp e d hsd
          · have hU2 : U'' = l'.post := hU
            rw [← hU2]
            exact hU''
        obtain ⟨w₁, hw₁, hr₁⟩ := hp.lift hθ hK (.cons ht' hw'') ⟨d, hl', hr''⟩
        exact ⟨y, U, hyU, hθ.entails hKU hK, w₁, hw₁, hr₁⟩

/-- **Soundness**: if `check` accepts a certificate, and the theory is sound,
`X` is within `Y`. -/
theorem check_sound (hθ : θ.Sound M loc) {c : Cert} (h : check θ X Y false c = true) :
    Rel.Sub (X.denote (Label.denote M)) (Y.denote (Label.denote M)) := by
  rintro x y ⟨q, hq, w, hw, hr⟩
  obtain ⟨j, m'', hj, hc⟩ := coveredBy_spec (check_spec h).1 _ (List.mem_map_of_mem hq)
  obtain ⟨y0, U, hyU, -, w', hw', hr'⟩ :=
    covers_claim hc (claim_all hθ h w j m'' hj) x x y hw (fun _ hp => by simp [initial] at hp)
      (fun hf => by simp at hf) hr
  simp only [initial] at hyU
  have := mem_canon hyU
  simp only [List.mem_map] at this
  obtain ⟨y1, hy1, hy1'⟩ := this
  cases hy1'
  exact ⟨_, hy1, w', hw', hr'⟩

/-- **Soundness, for cycles**: if `check` accepts a certificate in cycle mode,
and the theory is sound, each cycle of `X` is one of `Y`. -/
theorem check_sound_cycle (hθ : θ.Sound M loc) {c : Cert} (h : check θ X Y true c = true) :
    ∀ a, X.denote (Label.denote M) a a → Y.denote (Label.denote M) a a := by
  rintro a ⟨q, hq, w, hw, hr⟩
  obtain ⟨j, m'', hj, hc⟩ := coveredBy_spec (check_spec h).1 _ (List.mem_map_of_mem hq)
  obtain ⟨y0, U, hyU, -, w', hw', hr'⟩ :=
    covers_claim hc (claim_all hθ h w j m'' hj) a a a hw (fun _ hp => by simp [initial] at hp)
      (fun _ => ⟨fun _ => rfl, fun K0 hK0 => by simp [initial] at hK0, rfl⟩) hr
  simp only [initial] at hyU
  have := mem_canon hyU
  simp only [List.mem_map] at this
  obtain ⟨y1, hy1, hy1'⟩ := this
  cases hy1'
  exact ⟨_, hy1, w', hw', hr'⟩

/-- `prove`, which searches and checks, is as sound as `check`. -/
theorem prove_sound {hint : Option (Array (List Nat))} (hθ : θ.Sound M loc)
    (h : prove θ X Y false hint = true) :
    Rel.Sub (X.denote (Label.denote M)) (Y.denote (Label.denote M)) := by
  unfold prove at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · split at h
      · exact check_sound hθ h
      · simp at h
    · simp at h
  · split at h
    · exact check_sound hθ h
    · simp at h

theorem prove_sound_cycle {hint : Option (Array (List Nat))} (hθ : θ.Sound M loc)
    (h : prove θ X Y true hint = true) :
    ∀ a, X.denote (Label.denote M) a a → Y.denote (Label.denote M) a a := by
  unfold prove at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · split at h
      · exact check_sound_cycle hθ h
      · simp at h
    · simp at h
  · split at h
    · exact check_sound_cycle hθ h
    · simp at h

end Claim

end Guarded

end KaterCert
