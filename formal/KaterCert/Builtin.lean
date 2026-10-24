import KaterCert.Theory

/-!
# Kater's builtin theory, and a module's

The theory the checkers are run with: the facts Kater's `Theory` states about
its builtin relations and predicates (`src/Builtins.cpp`, `src/Theory.cpp`),
and those a module adds: its `disjoint` declarations, the domains, codomains
and incompatibilities its assumptions state, and the per-location variants of
its relations. The model proves the builtin facts of every graph, and a
module's facts of every graph that satisfies the module's declarations and
assumptions.

This mirrors the C++ regions `PredicateIDs` (`src/Predicate.hpp`),
`RelationIDs` (`src/Relation.hpp`), `BuiltinRelations`, `BuiltinPredicates`
(`src/Builtins.cpp`), and `RelationInclusion` (`src/Theory.cpp`):
`scripts/check-mirrors.sh` reports when they change.
-/

namespace KaterCert

namespace Builtin

/-! ## Ids -/

/-- Kater's builtin predicates (`Predicate::BuiltinID`), by id. -/
inductive Pred where
  | NA | ATOM | RLX | ACQ | REL | SC | W | R | EXCL | NEXCL | F | TC | TJ | TB | TE | TK
  | ALLOC | FREE | HPRET | PROT | HPPROT | NOTHPPROT | LK | UL | PLK | NPLK | MB | ME
  | HEAP | REC | D | DEP | LOC
  deriving DecidableEq, Repr, Inhabited

/-- Kater's builtin relations (`Relation::BuiltinID`, without the markers
`PerLocBegin`, `WithinPoBegin`, `PerLocLast` and `WithinPoLast`), by id. -/
inductive Rel where
  | same_thread | si | last_na_reads | last_na_writes | last_at_reads | last_at_writes
  | unprotected | alloc | free | retire | loc_overlap | tc | tj | lin
  | rf | mo_imm | mo | fr_imm | fr | rfe | moe | fre
  | ctrl | addr | data | pctrl | rfi | moi | fri | detour | rmw | po_loc_imm | po_loc
  | po_imm | po | any
  deriving DecidableEq, Repr, Inhabited

def Pred.all : List Pred :=
  [.NA, .ATOM, .RLX, .ACQ, .REL, .SC, .W, .R, .EXCL, .NEXCL, .F, .TC, .TJ, .TB, .TE, .TK,
   .ALLOC, .FREE, .HPRET, .PROT, .HPPROT, .NOTHPPROT, .LK, .UL, .PLK, .NPLK, .MB, .ME,
   .HEAP, .REC, .D, .DEP, .LOC]

/-- The id of a builtin predicate: its place in the enumeration. -/
def Pred.id (p : Pred) : Int :=
  match p with
  | .NA => 0 | .ATOM => 1 | .RLX => 2 | .ACQ => 3 | .REL => 4 | .SC => 5 | .W => 6 | .R => 7
  | .EXCL => 8 | .NEXCL => 9 | .F => 10 | .TC => 11 | .TJ => 12 | .TB => 13 | .TE => 14
  | .TK => 15 | .ALLOC => 16 | .FREE => 17 | .HPRET => 18 | .PROT => 19 | .HPPROT => 20
  | .NOTHPPROT => 21 | .LK => 22 | .UL => 23 | .PLK => 24 | .NPLK => 25 | .MB => 26
  | .ME => 27 | .HEAP => 28 | .REC => 29 | .D => 30 | .DEP => 31 | .LOC => 32

def Rel.all : List Rel :=
  [.same_thread, .si, .last_na_reads, .last_na_writes, .last_at_reads, .last_at_writes,
   .unprotected, .alloc, .free, .retire, .loc_overlap, .tc, .tj, .lin, .rf, .mo_imm, .mo,
   .fr_imm, .fr, .rfe, .moe, .fre, .ctrl, .addr, .data, .pctrl, .rfi, .moi, .fri, .detour,
   .rmw, .po_loc_imm, .po_loc, .po_imm, .po, .any]

/-- The id of a builtin relation: its place in Kater's enumeration, markers
included. -/
def Rel.id (r : Rel) : Int :=
  match r with
  | .same_thread => 0 | .si => 1 | .last_na_reads => 2 | .last_na_writes => 3
  | .last_at_reads => 4 | .last_at_writes => 5 | .unprotected => 6 | .alloc => 7
  | .free => 8 | .retire => 9 | .loc_overlap => 10 | .tc => 11 | .tj => 12 | .lin => 13
  | .rf => 15 | .mo_imm => 16 | .mo => 17 | .fr_imm => 18 | .fr => 19 | .rfe => 20
  | .moe => 21 | .fre => 22 | .ctrl => 24 | .addr => 25 | .data => 26 | .pctrl => 27
  | .rfi => 28 | .moi => 29 | .fri => 30 | .detour => 31 | .rmw => 32 | .po_loc_imm => 33
  | .po_loc => 34 | .po_imm => 36 | .po => 38 | .any => 39

/-- The builtin predicate of an id, if it is one. -/
def Pred.ofId (i : Int) : Option Pred := Pred.all.find? (·.id == i)

/-- The builtin relation of an id, if it is one. -/
def Rel.ofId (i : Int) : Option Rel := Rel.all.find? (·.id == i)

/-! ## Predicates -/

/-- Kater's sub-predicates (`subsetPredSets_`): `p` implies `q`. -/
def subPred : Pred → Pred → Bool
  | .RLX, .ATOM | .ACQ, .ATOM | .REL, .ATOM => true
  | .SC, .ATOM | .SC, .ACQ | .SC, .REL => true
  | .R, .DEP | .R, .LOC | .ALLOC, .DEP | .ALLOC, .LOC => true
  | .FREE, .LOC | .HPPROT, .LOC | .W, .LOC => true
  | _, _ => false

/-- Kater's sets of pairwise disjoint builtin predicates (`disjointPredSets_`). -/
def disjointSets : List (List Pred) :=
  [[.R, .W, .F, .TC, .TB, .TE, .TJ, .TK, .ALLOC, .FREE, .MB, .ME],
   [.NA, .ATOM],
   [.NA, .RLX, .ACQ],
   [.NA, .RLX, .REL],
   [.NEXCL, .EXCL],
   [.PLK, .NPLK],
   [.TB, .REL], [.TJ, .REL],
   [.TC, .ACQ], [.TE, .ACQ],
   [.DEP, .W, .F, .TC, .TB, .TE, .TJ, .TK, .FREE],
   [.LOC, .F, .TC, .TB, .TE, .TJ, .TK]]

/-! ## Relations -/

/-- Where the steps of a builtin relation start and end (`builtinRelations`'
`dom` and `codom`). -/
def domains : Rel → List Pred × List Pred
  | .rmw => ([.R, .EXCL], [.W, .EXCL])
  | .ctrl | .addr | .data | .pctrl => ([.DEP], [])
  | .alloc => ([.ALLOC], [])
  | .free => ([.FREE], [])
  | .retire => ([.HPRET], [])
  | .rf | .rfe | .rfi | .detour => ([.W], [.R])
  | .tc => ([.TC], [.TB])
  | .tj => ([.TE], [.TJ])
  | .lin => ([.ME], [.MB])
  | .mo_imm | .mo | .moe | .moi => ([.W], [.W])
  | .fr_imm | .fr | .fre | .fri => ([.R], [.W])
  | _ => ([], [])

/-- The builtin relations that keep the location (`RelLocInfo::KeepsLoc`). -/
def keepsLocInfo : Rel → Bool
  | .po_loc_imm | .po_loc | .rmw | .last_na_reads | .last_na_writes | .last_at_reads
  | .last_at_writes | .unprotected | .free | .retire | .loc_overlap | .rf | .rfe | .rfi
  | .mo_imm | .mo | .moe | .moi | .fr_imm | .fr | .fre | .fri | .detour => true
  | _ => false

/-- The builtin relations within a thread (`WithinPoBegin` to
`WithinPoLast`). -/
def withinPo : Rel → Bool
  | .ctrl | .addr | .data | .pctrl | .rfi | .moi | .fri | .detour | .rmw | .po_loc_imm
  | .po_loc | .po_imm => true
  | _ => false

/-- Kater's inclusions between builtin relations of the same direction
(`Theory::isIncludedIn` of relations), but those of a per-location variant
in its relation. -/
def relIncl : Rel → Rel → Bool
  | a, b =>
    a == b || b == .any ||
    (b == .rf && (a == .rfi || a == .rfe)) ||
    (b == .mo && (a == .moi || a == .moe || a == .mo_imm)) ||
    (b == .fr && (a == .fri || a == .fre || a == .fr_imm)) ||
    (b == .po && withinPo a) ||
    (b == .po_loc && withinPo a && keepsLocInfo a)

/-- The builtin per-location variants (`registerPerLocPair`). -/
def perLoc : Rel → Option Rel
  | .po_imm => some .po_loc_imm
  | .po => some .po_loc
  | _ => none

/-- Kater's eco relations (`Theory::isEco`): within `rf`, `mo` or `fr`. -/
def isEco (r : Rel) : Bool := relIncl r .rf || relIncl r .mo || relIncl r .fr

end Builtin

/-- What a module adds to the builtin theory. -/
structure Decls where
  /-- Its `disjoint` declarations, and the incompatibilities of two
  predicates its assumptions state (`[A;B] = 0`). -/
  disjoint : List (List Int) := []
  /-- The incompatibilities of other numbers of predicates its assumptions
  state. -/
  invalid : List (List Int) := []
  /-- Its relations' per-location variants. -/
  perLoc : List (Int × Int) := []
  /-- The domains and codomains its assumptions state (`r <= [A];r;[B]`). -/
  domains : List (Int × List Predicate × List Predicate) := []
  deriving Repr, Inhabited

/-- A module's declarations, well-formed: its relations' per-location
variants are of user relations, and each relation has at most one, which is
no relation's base. -/
def Decls.wf (d : Decls) : Bool :=
  d.perLoc.all (fun (r, v) => r < 0 && v < 0 && r != v) &&
    (d.perLoc.map (·.1)).eraseDups.length == d.perLoc.length &&
    (d.perLoc.map (·.2)).eraseDups.length == d.perLoc.length &&
    d.perLoc.all (fun (_, v) => !(d.perLoc.any (·.1 == v)))

/-- What a module's declarations say: its `disjoint` predicates are pairwise
disjoint, its incompatible predicates hold of no event together, and its
relations have the domains and codomains its assumptions state. -/
def Decls.Hold {E : Type} (d : Decls) (M : Interp E) : Prop :=
  (∀ D ∈ d.disjoint, ∀ p ∈ D, ∀ q ∈ D, p ≠ q → ∀ e, ¬ (M.pred p e ∧ M.pred q e)) ∧
    (∀ I ∈ d.invalid, ∀ e, ¬ ∀ i ∈ I, M.pred i e) ∧
    (∀ t ∈ d.domains, ∀ x y, M.rel t.1 x y →
      Checks M t.2.1 x ∧ Checks M t.2.2 y)


namespace Theory

open Builtin

/-- The predicates of a builtin. -/
def plain (p : Builtin.Pred) : Predicate := { id := p.id, complement := false }

/-- `p` implies `q`, both plain predicates: the same, or a builtin
sub-predicate. -/
def subPredId (p q : Int) : Bool :=
  p == q || match Pred.ofId p, Pred.ofId q with
    | some a, some b => subPred a b
    | _, _ => false

/-- Kater's theory of a module: the builtin facts, and the module's. -/
def ofDecls (d : Decls) : Theory where
  predIncl p q :=
    p == q || (!p.complement && !q.complement && subPredId p.id q.id) ||
      (p.complement && q.complement && subPredId q.id p.id)
  unsat ps :=
    ps.any (fun p => ps.any fun q => p.id == q.id && p.complement != q.complement) ||
    (d.disjoint ++ disjointSets.map (·.map Pred.id)).any (fun D =>
      ps.any fun p => ps.any fun q =>
        !p.complement && !q.complement && p.id != q.id &&
        D.any fun a => D.any fun b => a != b && subPredId p.id a && subPredId q.id b) ||
    d.invalid.any (fun I => I.all fun i => ps.any fun p => !p.complement && p.id == i)
  relIncl r s :=
    r == s || (match Rel.ofId s.id with | some .any => true | _ => false) ||
    (r.inverse == s.inverse &&
      ((d.perLoc.any fun (b, v) => b == s.id && v == r.id) ||
       (match Rel.ofId r.id, Rel.ofId s.id with
        | some a, some b =>
          (Builtin.perLoc b == some a && b != .po_imm) || Builtin.relIncl a b
        | _, _ => false)))
  dom r :=
    let (dom, codom) := match Rel.ofId r.id with
      | some b => ((domains b).1.map plain, (domains b).2.map plain)
      | none => (d.domains.filterMap fun (i, p, _) => if i == r.id then some p else none).flatten
          |> fun p => (p, (d.domains.filterMap fun (i, _, q) => if i == r.id then some q else none).flatten)
    if r.inverse then codom else dom
  codom r :=
    let (dom, codom) := match Rel.ofId r.id with
      | some b => ((domains b).1.map plain, (domains b).2.map plain)
      | none => (d.domains.filterMap fun (i, p, _) => if i == r.id then some p else none).flatten
          |> fun p => (p, (d.domains.filterMap fun (i, _, q) => if i == r.id then some q else none).flatten)
    if r.inverse then dom else codom
  perLoc r :=
    match Rel.ofId r.id with
    | some b => (Builtin.perLoc b).map fun v => { id := v.id, inverse := r.inverse }
    | none => (d.perLoc.find? (·.1 == r.id)).map fun (_, v) => { id := v, inverse := r.inverse }
  keepsLoc r :=
    match Rel.ofId r.id with
    | some b => isEco b
    | none => false
  reflexive r := match Rel.ofId r.id with | some .any => true | _ => false

end Theory

end KaterCert
