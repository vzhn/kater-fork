import KaterCert.Builtin
import KaterCert.Exp

/-!
# The model: execution graphs

What Kater's builtins mean, as `doc/verification.md` (The reference
semantics) describes it and the oracle implements it (`tests/oracle/Graph.cpp`,
`tests/oracle/Semantics.cpp`): events with a kind, an ordering, a location
and a few flags, program order within threads, `rf`, `mo`, the dependencies,
`tc`, `tj`, `lin`, and the order of GenMC's execution state, with the axioms
every graph GenMC builds satisfies; and the builtin predicates and relations
defined from them. Initial writes are implicit: a read without an `rf` edge
reads the initial value, and is `fr`-before every write of its location.

`WF` has only the axioms the facts the checkers rest on need. The oracle's
others are left out: the orderings of fences and of the events that are not
atomic, which events are exclusive and which abstract locks, that program
order is irreflexive and within threads, and the axioms of heap blocks, of
the execution state's order and of GenMC's `hb`. The theorems then hold of
more graphs than GenMC builds, which is the stronger claim. The meaning of `same-thread` is being in the
same thread; `si` and `loc-overlap`, and the predicates `LK` and `UL`, which
the oracle gives no meaning, are any relation and any predicates.

A module's own relations and predicates are any relations and predicates
(`User`), but the per-location variant `r-loc` of a relation `r`, which is
`r` between events on the same location.

`ModelEval` decides the builtins and the axioms on finite graphs, and
`kater-model-check` compares them with the oracle's on the graphs it
enumerates (`doc/verification.md`, Whole proofs).
-/

namespace KaterCert

namespace Model

/-- The kinds of events (GenMC's label classes). -/
inductive Kind where
  | R | W | F | TC | TB | TJ | TE | TK | ALLOC | FREE | HPRET | HPPROTECT | MB | ME | OTHER
  deriving DecidableEq, Repr

/-- The orderings of events. -/
inductive Order where
  | NA | RLX | ACQ | REL | ACQ_REL | SC
  deriving DecidableEq, Repr

/-- An execution graph. -/
structure Graph where
  E : Type
  kind : E → Kind
  order : E → Order
  /-- Part of a read-modify-write. -/
  excl : E → Prop
  /-- The location of an access, or the block of an allocation, a free, a
  retire or a protection. -/
  loc : E → Nat
  thread : E → Nat
  po : E → E → Prop
  rf : E → E → Prop
  mo : E → E → Prop
  ctrl : E → E → Prop
  addr : E → E → Prop
  data : E → E → Prop
  pctrl : E → E → Prop
  tc : E → E → Prop
  tj : E → E → Prop
  lin : E → E → Prop
  /-- The hazard pointer of a protection. -/
  hp : E → Nat
  /-- The order of GenMC's execution state. -/
  added : E → E → Prop
  /-- GenMC's hb, which the state records accesses with. -/
  hb : E → E → Prop
  durable : E → Prop
  recovery : E → Prop
  abstractLock : E → Prop
  dependableOther : E → Prop
  si : E → E → Prop
  locOverlap : E → E → Prop
  lk : E → Prop
  ul : E → Prop

namespace Graph

variable (G : Graph)

def isKind (k : Kind) (e : G.E) : Prop := G.kind e = k

/-- Reads and writes have a location. -/
def located (e : G.E) : Prop := G.kind e = .R ∨ G.kind e = .W

/-- So do allocations, frees, retires and protections: of a block. -/
def hasLocation (e : G.E) : Prop :=
  G.located e ∨ G.kind e = .ALLOC ∨ G.kind e = .FREE ∨ G.kind e = .HPRET ∨
    G.kind e = .HPPROTECT

/-- Being on the same location; every event is on its own. -/
def sameLoc (x y : G.E) : Prop := x = y ∨ (G.located x ∧ G.located y ∧ G.loc x = G.loc y)

/-- Being of the same block. -/
def sameBlock (x y : G.E) : Prop :=
  (x = y ∧ G.hasLocation x) ∨ (x ≠ y ∧ G.hasLocation x ∧ G.hasLocation y ∧ G.loc x = G.loc y)

def sameThread (x y : G.E) : Prop := G.thread x = G.thread y

/-- R, ALLOC, and some OTHER events: what dependencies start from. -/
def dependable (e : G.E) : Prop :=
  G.kind e = .R ∨ G.kind e = .ALLOC ∨ G.dependableOther e

def atLeastAcq (e : G.E) : Prop := G.order e = .ACQ ∨ G.order e = .ACQ_REL ∨ G.order e = .SC

def atLeastRel (e : G.E) : Prop := G.order e = .REL ∨ G.order e = .ACQ_REL ∨ G.order e = .SC

/-! ## The derived relations -/

def poImm (x y : G.E) : Prop := G.po x y ∧ ¬ ∃ z, G.po x z ∧ G.po z y

def poLoc (x y : G.E) : Prop := G.po x y ∧ G.sameLoc x y

/-- The next event of the thread on the same location: it skips the events
of other locations. -/
def poLocImm (x y : G.E) : Prop := G.poLoc x y ∧ ¬ ∃ z, G.po x z ∧ G.po z y ∧ G.sameLoc x z

/-- A read of the initial value has no `rf` edge. -/
def readsInit (r : G.E) : Prop := ¬ ∃ w, G.rf w r

/-- From a read to the writes `mo`-after its source, or to all writes of
its location if it reads the initial value. -/
def fr (r w : G.E) : Prop :=
  r ≠ w ∧ G.kind r = .R ∧ G.kind w = .W ∧ G.sameLoc r w ∧
    (G.readsInit r ∨ ∃ s, G.rf s r ∧ G.mo s w)

def moImm (x y : G.E) : Prop := G.mo x y ∧ ¬ ∃ z, G.mo x z ∧ G.mo z y

def frImm (x y : G.E) : Prop := G.fr x y ∧ ¬ ∃ z, G.fr x z ∧ G.mo z y

/-- An exclusive read and the exclusive write right after it. -/
def rmw (x y : G.E) : Prop :=
  G.poImm x y ∧ G.kind x = .R ∧ G.excl x ∧ G.kind y = .W ∧ G.excl y ∧ G.sameLoc x y

/-- GenMC's detour: a write and a `po`-later read of its location that reads
from another write. -/
def detour (w r : G.E) : Prop :=
  G.kind w = .W ∧ G.kind r = .R ∧ G.poLoc w r ∧ ¬ G.rf w r

def external (r : G.E → G.E → Prop) (x y : G.E) : Prop := r x y ∧ ¬ G.sameThread x y

def internal (r : G.E → G.E → Prop) (x y : G.E) : Prop := r x y ∧ G.sameThread x y

/-! ## Heap blocks and GenMC's execution state -/

def heap (e : G.E) : Prop := ∃ a, G.kind a = .ALLOC ∧ G.sameBlock a e

def memLabel (e : G.E) : Prop :=
  G.located e ∨ G.kind e = .ALLOC ∨ G.kind e = .FREE ∨ G.kind e = .HPRET

def sameHp (x y : G.E) : Prop := x = y ∨ G.hp x = G.hp y

/-- GenMC's `isHazptrProtected()`: the closest protection of the event's
block before it in `po`, through a hazard pointer that protects nothing else
before the event. -/
def hpProtected (e : G.E) : Prop :=
  ∃ p, G.po p e ∧ G.kind p = .HPPROTECT ∧ G.sameBlock p e ∧
    ¬ ∃ q, G.po p q ∧ G.po q e ∧ G.kind q = .HPPROTECT ∧ (G.sameBlock q e ∨ G.sameHp q p)

def freeing (f : G.E) : Prop := G.kind f = .FREE ∨ G.kind f = .HPRET

/-- The last free or retire of the event's block before it in the state. -/
def lastFreeing (f e : G.E) : Prop :=
  f ≠ e ∧ G.freeing f ∧ G.memLabel e ∧ G.sameBlock f e ∧ G.added f e ∧
    ¬ ∃ g, g ≠ f ∧ g ≠ e ∧ G.freeing g ∧ G.sameBlock g e ∧ G.added f g ∧ G.added g e

def allocRel (a e : G.E) : Prop :=
  a ≠ e ∧ G.kind a = .ALLOC ∧ G.memLabel e ∧ G.sameBlock a e

def freeRel (f e : G.E) : Prop := G.lastFreeing f e ∧ G.kind f = .FREE

def retireRel (f e : G.E) : Prop := G.lastFreeing f e ∧ G.kind f = .HPRET

/-- `ExecutionState::isProtected()`: some hazard pointer protects the block
when the event enters the state, its last protection before being of it. -/
def protectedWhenAdded (e : G.E) : Prop :=
  ∃ p, p ≠ e ∧ G.kind p = .HPPROTECT ∧ G.sameBlock p e ∧ G.added p e ∧
    ¬ ∃ q, q ≠ p ∧ q ≠ e ∧ G.kind q = .HPPROTECT ∧ G.sameHp q p ∧ G.added p q ∧ G.added q e

def access (e : G.E) : Prop := G.located e

def lifecycle (e : G.E) : Prop := G.kind e = .ALLOC ∨ G.kind e = .FREE ∨ G.kind e = .HPRET

/-- The positional relations (`last_na_reads`, ..., `unprotected`): to an
event from the events of its location the state recorded before it, those
`hb`-maximal (for `last_na_writes`, the last). `recorded` says which events
a relation records, `asks` which ask for them, `byHb` whether it keeps the
`hb`-maximal ones. -/
def positional (recorded asks : G.E → Prop) (byHb : Bool) (x y : G.E) : Prop :=
  x ≠ y ∧ asks y ∧ recorded x ∧ G.sameBlock x y ∧ G.added x y ∧
    ¬ ∃ z, z ≠ x ∧ z ≠ y ∧ recorded z ∧ G.sameBlock z y ∧ G.added x z ∧ G.added z y ∧
      (byHb = false ∨ G.hb x z)

/-! ## The builtins -/

/-- What a builtin predicate means of an event. -/
def pred : Builtin.Pred → G.E → Prop
  | .NA => fun e => G.order e = .NA
  | .ATOM => fun e => G.order e ≠ .NA
  | .RLX => fun e => G.order e = .RLX
  | .ACQ => G.atLeastAcq
  | .REL => G.atLeastRel
  | .SC => fun e => G.order e = .SC
  | .W => G.isKind .W
  | .R => G.isKind .R
  | .EXCL => G.excl
  | .NEXCL => fun e => ¬ G.excl e
  | .F => G.isKind .F
  | .TC => G.isKind .TC
  | .TJ => G.isKind .TJ
  | .TB => G.isKind .TB
  | .TE => G.isKind .TE
  | .TK => G.isKind .TK
  | .ALLOC => G.isKind .ALLOC
  | .FREE => G.isKind .FREE
  | .HPRET => G.isKind .HPRET
  | .PROT => G.isKind .HPPROTECT
  | .HPPROT => fun e => G.located e ∧ G.heap e ∧ G.hpProtected e
  | .NOTHPPROT => fun e =>
    G.located e ∧ G.heap e ∧ (∃ r, G.retireRel r e) ∧ ¬ G.hpProtected e
  | .LK => G.lk
  | .UL => G.ul
  | .PLK => G.abstractLock
  | .NPLK => fun e => ¬ G.abstractLock e
  | .MB => G.isKind .MB
  | .ME => G.isKind .ME
  | .HEAP => fun e => G.located e ∧ G.heap e
  | .REC => G.recovery
  | .D => G.durable
  | .DEP => G.dependable
  | .LOC => G.hasLocation

/-- What a builtin relation means. -/
def rel : Builtin.Rel → Rel G.E
  | .same_thread => G.sameThread
  | .si => G.si
  | .last_na_reads => G.positional (fun e => G.kind e = .R ∧ G.order e = .NA)
      (fun e => G.access e ∨ G.lifecycle e) true
  | .last_na_writes => G.positional (fun e => G.kind e = .W ∧ G.order e = .NA)
      (fun e => G.access e ∨ G.lifecycle e) false
  | .last_at_reads => G.positional (fun e => G.kind e = .R ∧ G.order e ≠ .NA)
      (fun e => G.access e ∨ G.lifecycle e) true
  | .last_at_writes => G.positional (fun e => G.kind e = .W ∧ G.order e ≠ .NA)
      (fun e => G.access e ∨ G.lifecycle e) true
  | .unprotected => G.positional (fun e => G.access e ∧ ¬ G.protectedWhenAdded e)
      G.lifecycle true
  | .alloc => G.allocRel
  | .free => G.freeRel
  | .retire => G.retireRel
  | .loc_overlap => G.locOverlap
  | .tc => G.tc
  | .tj => G.tj
  | .lin => G.lin
  | .rf => G.rf
  | .mo_imm => G.moImm
  | .mo => G.mo
  | .fr_imm => G.frImm
  | .fr => G.fr
  | .rfe => G.external G.rf
  | .moe => G.external G.mo
  | .fre => G.external G.fr
  | .ctrl => G.ctrl
  | .addr => G.addr
  | .data => G.data
  | .pctrl => G.pctrl
  | .rfi => G.internal G.rf
  | .moi => G.internal G.mo
  | .fri => G.internal G.fr
  | .detour => G.detour
  | .rmw => G.rmw
  | .po_loc_imm => G.poLocImm
  | .po_loc => G.poLoc
  | .po_imm => G.poImm
  | .po => G.po
  | .any => fun _ _ => True

/-! ## The axioms -/

/-- What every graph GenMC builds satisfies, of what the facts need
(`doc/verification.md`, Execution graphs). -/
structure WF : Prop where
  /-- Orderings by kind: thread creations, finishes and protections
  release; starts and joins acquire. -/
  order_rel : ∀ e, G.kind e = .TC ∨ G.kind e = .TE ∨ G.kind e = .HPPROTECT → G.order e = .REL
  order_acq : ∀ e, G.kind e = .TB ∨ G.kind e = .TJ → G.order e = .ACQ
  /-- Program order: transitive, and total within each thread. -/
  po_trans : ∀ x y z, G.po x y → G.po y z → G.po x z
  po_total : ∀ x y, G.thread x = G.thread y → x ≠ y → G.po x y ∨ G.po y x
  /-- `rf` from a write to a read of its location, at most one per read. -/
  rf_kinds : ∀ w r, G.rf w r → G.kind w = .W ∧ G.kind r = .R ∧ G.loc w = G.loc r
  rf_unique : ∀ w w' r, G.rf w r → G.rf w' r → w = w'
  /-- `mo` a strict total order on the writes of each location. -/
  mo_kinds : ∀ x y, G.mo x y → G.kind x = .W ∧ G.kind y = .W ∧ G.loc x = G.loc y
  mo_irrefl : ∀ x, ¬ G.mo x x
  mo_trans : ∀ x y z, G.mo x y → G.mo y z → G.mo x z
  /-- `rf`, `mo` and `fr` never go backwards in `po`. -/
  rf_po : ∀ x y, G.rf x y → ¬ G.po y x
  mo_po : ∀ x y, G.mo x y → ¬ G.po y x
  fr_po : ∀ x y, G.fr x y → ¬ G.po y x
  /-- Dependencies go forward in `po`, out of dependable events. -/
  ctrl_po : ∀ x y, G.ctrl x y → G.po x y ∧ G.dependable x
  addr_po : ∀ x y, G.addr x y → G.po x y ∧ G.dependable x
  data_po : ∀ x y, G.data x y → G.po x y ∧ G.dependable x
  pctrl_po : ∀ x y, G.pctrl x y → G.po x y ∧ G.dependable x
  dependableOther_kind : ∀ e, G.dependableOther e → G.kind e = .OTHER
  /-- Thread creation goes from a creation to a start, a join from a finish
  to a join; `lin` goes from method ends to method begins. -/
  tc_kinds : ∀ x y, G.tc x y → G.kind x = .TC ∧ G.kind y = .TB
  tj_kinds : ∀ x y, G.tj x y → G.kind x = .TE ∧ G.kind y = .TJ
  lin_kinds : ∀ x y, G.lin x y → G.kind x = .ME ∧ G.kind y = .MB

/-! ## Meaning -/

/-- A module's own predicates and relations. -/
structure User (E : Type) where
  pred : Int → E → Prop
  rel : Int → Rel E

/-- What the ids of letters mean in `G`: the builtins, the module's own
predicates and relations, and the per-location variants `perLoc` lists, as
(relation, variant). An id that is neither a builtin nor negative means
nothing. -/
def interp (U : User G.E) (perLoc : List (Int × Int)) : Interp G.E where
  pred i := match Builtin.Pred.ofId i with
    | some p => G.pred p
    | none => if i < 0 then U.pred i else fun _ => False
  rel i := match Builtin.Rel.ofId i with
    | some r => G.rel r
    | none =>
      if i < 0 then
        match perLoc.find? (·.2 == i) with
        | some (b, _) => fun x y => U.rel b x y ∧ G.sameLoc x y
        | none => U.rel i
      else fun _ _ => False

end Graph

end Model

end KaterCert
