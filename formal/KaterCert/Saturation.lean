import KaterCert.Label
import KaterCert.NFA

/-!
# Evidence of the saturations

The evidence a saturation of a right-hand side records
(`SaturationEvidence`), and `Evidence.check`, the checker of
`tests/oracle/Chain.cpp` (`checkSaturation`): the same conditions in the same
order, with the same messages.

A saturation from automaton `N` to `M` assumes a hypothesis: that a letter
is transitive, that an automaton denotes no more than a word, or that an
automaton denotes nothing. The evidence gives each state of `M` a role,
which bounds what the words reaching it relate in terms of `N`
(`doc/verification.md`, Evidence of the saturations):

- `state n`: what the words reaching state `n` of `N` relate;
- `after n`: what those that reach `n` by a step reading the transitive
  letter relate;
- `copy j g`: what a word reaching the start of copy `g` of the hypothesis'
  automaton relates, followed by one of the automaton reaching its state `j`.

The check confirms, by local conditions, that every state of `M` is reached
by no more than its role bounds, and that the accepting ones are within what
`N` denotes.

This mirrors the C++ regions `SaturationEvidence` (`src/Saturation.hpp`) and
`checkSaturation` (`tests/oracle/Chain.cpp`): `scripts/check-mirrors.sh`
reports when they change.
-/

namespace KaterCert

/-- What a saturation assumes: that `letter` is transitive, that
`automaton` denotes no more than `word`, or that it denotes nothing. -/
inductive Hypothesis where
  | transitive
  | within
  | empty
  deriving DecidableEq, Repr

/-- What a state of the saturated automaton stands for. -/
inductive Role where
  /-- State `n` of the automaton saturated. -/
  | state (n : Nat)
  /-- State `n` of the automaton saturated, entered by the transitive letter. -/
  | after (n : Nat)
  /-- State `j` of the hypothesis' automaton, in copy `g` (any copy, for an
  empty hypothesis). -/
  | copy (j g : Nat)
  deriving DecidableEq, Repr

/-- A step of a copy's path: its letter and destination, and the predicates
of the hypothesis' word known of the event it leaves that it needs. -/
structure Step where
  letter : Label
  dest : Nat
  known : List Predicate
  deriving DecidableEq, Repr

/-- A copy of the hypothesis' automaton, from state `src` of the automaton
saturated to state `dst`, along a `path` of it that reads the word. -/
structure Copy where
  src : Nat
  dst : Nat
  path : List Step
  deriving Repr

/-- What a saturation from `N` to `M` records: its hypothesis, a role for
each state of `M`, the copies of the hypothesis' automaton, and the letter
inclusions the copies' paths take from the theory. -/
structure Evidence where
  hypothesis : Hypothesis
  letter : Label
  automaton : NFA Label
  word : List Label
  roles : Array Role
  copies : Array Copy
  /-- `(a, b)`: letter `a` is included in letter `b`. -/
  inclusions : List (Label × Label)

/-- Whether `A` has the step `q --a--> q'`. -/
def NFA.hasStep (A : NFA Label) (q : Nat) (a : Label) (q' : Nat) : Bool :=
  (A.trans q).any fun (b, d) => b == a && d == q'

/-- Whether the predicates `ps` are among `known`. -/
def knows (known ps : List Predicate) : Bool :=
  ps.all fun p => known.contains p

/-- Whether `path` reads `word`: walking both, a predicate of the word adds
its checks to what is `known` of the current event; a predicate `[Q]` of the
path needs `[K] <= [Q]` for the subset `K` of what is known its step
records; a relation `b` of the path needs the next letter of the word to be
a bare relation `r` with `[K];r <= b`, after which nothing is known. `incl`
says which letter inclusions hold. -/
def reads (incl : Label → Label → Bool) : List Predicate → List Label → List Step → Bool
  | known, a :: w, path =>
    if a.rel.isNone then reads incl (known ++ a.pre) w path
    else match path with
      | s :: path' =>
        if s.letter.rel.isNone then
          knows known s.known && incl ⟨none, s.known, []⟩ s.letter &&
            reads incl known (a :: w) path'
        else
          a.pre.isEmpty && a.post.isEmpty && knows known s.known &&
            incl ⟨a.rel, s.known, []⟩ s.letter && reads incl [] w path'
      | [] => false
  | known, [], s :: path' =>
    s.letter.rel.isNone && knows known s.known && incl ⟨none, s.known, []⟩ s.letter &&
      reads incl known [] path'
  | _, [], [] => true
termination_by _ w path => w.length + path.length

/-- Where `A` reads `path` to from `q`, if it does. -/
def NFA.walk (A : NFA Label) : Nat → List Step → Option Nat
  | q, [] => some q
  | q, s :: path => if A.hasStep q s.letter s.dest then A.walk s.dest path else none

namespace Evidence

variable (ev : Evidence) (N M : NFA Label)

/-- Copy `g`, or a copy anchored at state 0 with no path if there is none:
the checker accepts no role of a copy that is not there. -/
def copy (g : Nat) : Copy := ev.copies.getD g ⟨0, 0, []⟩

/-- The role of state `m` of the saturated automaton. -/
def role (m : Nat) : Role := ev.roles.getD m (.state 0)

/-- Whether letter `a` is within letter `b`: equal, or one of the inclusions. -/
def includes (a b : Label) : Bool := a == b || ev.inclusions.contains (a, b)

/-- Whether copy `g` can be left: its path is one of `N`, from its start to
its end, that reads the word. -/
def exits (g : Nat) : Bool :=
  N.walk (ev.copy g).src (ev.copy g).path == some (ev.copy g).dst &&
    reads ev.includes [] ev.word (ev.copy g).path

/-- The roles `state n` lifts to: itself, and the starting states of the
copies from `n`. -/
def liftsState (n : Nat) : List Role :=
  .state n ::
    if ev.hypothesis = .within then
      (List.range ev.copies.size).flatMap fun g =>
        if (ev.copy g).src == n then ev.automaton.start.map fun i => .copy i g else []
    else []

/-- The roles a role lifts to: itself, and those whose bound includes its
bound. -/
def lifts : Role → List Role
  | .state n => ev.liftsState n
  | .after n => .after n :: ev.liftsState n
  | .copy j g =>
    .copy j g ::
      if ev.hypothesis = .within && ev.automaton.isAccepting j && ev.exits N g then
        ev.liftsState (ev.copy g).dst
      else []

/-- Whether role `s` steps by letter `l` to role `t`. -/
def steps (s : Role) (l : Label) (t : Role) : Bool :=
  (l.rel.isNone && s == t) ||
    match s, t with
    | .state n, .state n' => N.hasStep n l n'
    | .state n, .after n' =>
      ev.hypothesis == .transitive && l == ev.letter && N.hasStep n l n'
    | .state _, .copy _ _ => false
    | .after n, .after n' => n' == n && ev.hypothesis == .transitive && l == ev.letter
    | .after _, _ => false
    | .copy j g, t =>
      (ev.hypothesis == .empty && ev.automaton.isAccepting j) ||
        match t with
        | .copy j' g' =>
          (ev.hypothesis == .empty && ev.automaton.start.contains j &&
              ev.automaton.start.contains j') ||
            ((ev.hypothesis == .empty || g == g') && ev.automaton.hasStep j l j')
        | _ => false

/-- Whether the hypothesis' automaton reads the empty word. -/
def readsEmpty : Bool := ev.automaton.start.any ev.automaton.isAccepting

/-- `Z`, and the ends of the copies from its states that can be left. -/
def identityStep (Z : List Nat) : List Nat :=
  Z ++ (List.range ev.copies.size).filterMap fun g =>
    if Z.contains (ev.copy g).src && ev.exits N g then some (ev.copy g).dst else none

/-- The states of `N` the identity reaches: the starting ones and, if the
automaton reads the empty word, the ends of the copies from them that can be
left, and so on. A round adds an end or adds nothing ever after, so as many
rounds as copies reach all. -/
def byIdentity : List Nat :=
  if ev.hypothesis = .within && ev.readsEmpty then
    (List.range (ev.copies.size + 1)).foldl (fun Z _ => ev.identityStep N Z) N.start
  else N.start

/-- Whether a role bounds the identity, given the states `Z` of `N` the
identity reaches. -/
def startable (Z : List Nat) : Role → Bool
  | .state n => Z.contains n
  | .after _ => false
  | .copy j g =>
    ev.automaton.start.contains j && (ev.hypothesis == .empty || Z.contains (ev.copy g).src)

/-- Whether a role's bound is within what `N` denotes. -/
def acceptable (r : Role) : Bool :=
  (ev.lifts N r).any fun
    | .state n => N.isAccepting n
    | .after _ => false
    | .copy j _ => ev.hypothesis == .empty && ev.automaton.isAccepting j

/-- Whether a role names states that are there, as its kind allows. -/
def inRange : Role → Bool
  | .state n => n < N.size
  | .after n => ev.hypothesis == .transitive && n < N.size
  | .copy j g =>
    (ev.hypothesis == .within || ev.hypothesis == .empty) && j < ev.automaton.size &&
      (ev.hypothesis == .empty || g < ev.copies.size)

/-- Why the evidence does not show that `M` denotes no more than `N`, if it
does not. The states are those with steps or acceptance: Kater's automata
have as many of one as of the other. -/
def check : Option String :=
  if ev.roles.size ≠ M.size then
    some "the roles are not over the saturated automaton's states"
  else
    ((List.range ev.copies.size).findSome? fun g =>
      if (ev.copy g).src ≥ N.size || (ev.copy g).dst ≥ N.size then
        some s!"copy {g} is anchored outside the automaton"
      else none) <|>
    ((List.range ev.roles.size).findSome? fun m =>
      if ev.inRange N (ev.role m) then none
      else some s!"the role of state {m} names nothing") <|>
    (let Z := ev.byIdentity N
     M.start.findSome? fun m =>
      if ev.startable Z (ev.role m) then none
      else some s!"starting state {m} is not justified") <|>
    ((List.range (max M.size M.accepting.size)).findSome? fun m =>
      if M.isAccepting m && !ev.acceptable N (ev.role m) then
        some s!"accepting state {m} is not justified"
      else
        let ups := ev.lifts N (ev.role m)
        (M.trans m).findSome? fun (a, m') =>
          if ups.any fun s => ev.steps N s a (ev.role m') then none
          else some s!"the step {m} --> {m'} is not justified")

end Evidence

end KaterCert
