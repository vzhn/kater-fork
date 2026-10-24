# Verifying Kater

Kater proves assertions about memory models and exports consistency checkers
for GenMC. A wrong "holds" is the worst failure it can have: a metatheoretic
result that is not true, or a checker that accepts executions the model
forbids. This document describes how Kater is checked against an independent
semantics, the contracts its decision procedure has to meet, how its exported
checkers are run against that semantics, whether the models let GenMC explore
them, and what the checking has found so far.

Almost everything here is *bounded* testing: a claim is refuted by a graph of
at most N events, or not refuted up to N. It finds bugs; it does not prove
their absence. The contracts below are the lemmas a proof has to establish
(see [Next steps](#next-steps)). The exception is the last step of a proof of
inclusion, whose certificates a checker proved sound in Lean checks (see
[The checker in Lean](#the-checker-in-lean)).

## The reference semantics

`tests/oracle` builds `kater-oracle`, which gives `.kat` its meaning on
execution graphs and searches, with Z3, for small graphs that refute what
Kater claims. It shares Kater's parser and AST, and nothing of its
inference: the Theory is consulted only for names, for the per-location
variants of user relations, and for the user's `disjoint` declarations.

### Execution graphs

A graph has N events, numbered thread by thread in program order (any graph
can be numbered so), so thread boundaries are the only unknown of `po`. Each
event has a kind, an ordering, and a few label flags; reads, writes,
allocations, frees, retires and protections have a location, and a
protection a hazard pointer. The base relations are `rf`, `mo`, the
dependencies, `tc`, `tj` and `lin`, and the order of GenMC's execution state
(below); everything else is derived.

The axioms are what every graph GenMC builds satisfies, taken from GenMC's
`Execution/EventLabel.hpp` and `Execution/ExecutionGraph.hpp`, not from
Kater's Theory:

| Axiom | Why it holds in GenMC |
|-------|-----------------------|
| One kind per event: R, W, F, TC, TB, TJ, TE, TK, ALLOC, FREE, HPRET, HPPROTECT, METHOD-BEGIN, METHOD-END or OTHER | label classes |
| Orderings by kind: fences acq/rel/acq_rel/sc; TC, TE, HPPROTECT rel; TB, TJ acq; TK, ALLOC, FREE, HPRET, METHOD-* na; R, W, OTHER any | label constructors |
| Only R and W are exclusive; an exclusive write follows (po-imm) an exclusive read of its location | RMWs are added as a read then a write |
| `rf` goes from a write to a read of the same location, at most one per read; a read without one reads the initial value | `getRf()` |
| `mo` is a strict total order on the writes of each location | coherence order |
| `rf`, `mo` and `fr` never go backwards in `po` | rf and coherence choices respect `hb ⊇ po` |
| Dependencies go forward in `po`, out of dependable events (R, ALLOC, some OTHER) | `isDependable()` |
| `tc`, `tj` cross threads, from TC to TB and TE to TJ; `lin` goes from METHOD-END to METHOD-BEGIN | label kinds |
| R, W, ALLOC, FREE, HPRET and HPPROTECT have a location; one an ALLOC is of is a heap block, with one ALLOC, and FREE, HPRET and HPPROTECT are of heap blocks | `MemLabel::getAddr()`, `HpProtectLabel::getProtectedAddr()`; `free()` and the like look up the block's allocation |
| A block's ALLOC precedes its other events in `po \| rf \| tc \| tj` | a thread reaches a block through the address its allocation returned |
| GenMC's execution state holds the events in a strict total order: each after its `po` predecessors and its block's ALLOC, and, without a cycle of `po \| rf \| tc \| tj`, after the events it reads from, was created by or joins | `GenMCDriver` records each event as it adds it, and `reconstructState()` rebuilds the state in such an order on a restart |

Initial writes are implicit: a read of the initial value has no `rf` edge and
is `fr`-before every write to its location.

GenMC's memory-error checks read what its driver keeps in an execution state
(`ExecutionState`): the allocations, the frees and retires, the protections
of the hazard pointers, and the last accesses of each location. An event
GenMC checks sees the events before it there (`checkForRaces()`), so the
positional builtins are relative to the order of the state, and to GenMC's
hb: the view the model names `hb` (`getHbView()`), with which the state
records each access; in a module without one, any strict order between
`po` and `(po | rf | tc | tj | lin)+`.

The builtins mean what GenMC computes:

| Builtin | Meaning |
|---------|---------|
| `po`, `po-imm` | forward in a thread; the next event of the thread |
| `po-loc` | `po` between accesses of the same location (`poloc_succs`) |
| `po-loc-imm` | the next event of the thread *on the same location* (`poloc_imm_succ`): it skips the events of other locations, so it is not `po-imm & loc` |
| `rfe`/`rfi`, `moe`/`moi`, `fre`/`fri` | the relation across / within threads |
| `fr` | from a read to the writes `mo`-after its source, or to all writes of the location if it reads the initial value |
| `mo-imm`, `fr-imm` | immediate successors in `mo`, in `fr` |
| `rmw` | an exclusive read and the exclusive write right after it |
| `detour` | GenMC's: a write and a `po`-later read of its location that reads from another write |
| `any` | all pairs |
| `ctrl`, `addr`, `data`, `pctrl`, `tc`, `tj`, `lin` | uninterpreted, within the axioms above |
| `alloc` | from a block's ALLOC to its R, W, FREE and HPRET (`alloc_pos()`) |
| `free`, `retire` | to an event from the last FREE or HPRET of its block before it in the state, if a FREE, or an HPRET (`free_pos()`, `retire_pos()`: after a retire, a free is no double free) |
| `last_na_reads`, `last_at_reads`, `last_at_writes` | to an event from the NA reads, the atomic reads, the atomic writes of its location before it in the state, the hb-maximal ones (`pomax_*_pos()`: recording an access drops the ones in its hb view) |
| `last_na_writes` | to an event from the last NA write of its location before it in the state |
| `unprotected` | to a block's ALLOC, FREE and HPRET from its hb-maximal accesses before them in the state that no hazard pointer protected when they entered it (`unprotected_pos()`) |
| `HEAP` | an access of a heap block |
| `HPPROT` | an access of a heap block whose closest HPPROTECT of the block before it in `po` is through a hazard pointer that protects nothing later before it (`isHazptrProtected()`) |
| `NOTHPPROT` | an access of a block retired before it in the state (`retire_pos()`), not `HPPROT` |

`same-thread`, `si` and `loc-overlap` have no meaning in the oracle;
constraints that use them are reported as unsupported. User relations and
predicates are uninterpreted, subject to the module's `assume` and
`disjoint` statements. The per-location variant `r-loc` of a user relation
`r` is `r & loc`.

Conventions:

- Every event is on the same location as itself. This only matters for the
  per-location variants of user relations, since the builtin ones are
  irreflexive, and it is what `saturateLoc` assumes.
- `A & id <= B` means `(A & id) ⊆ B`.
- `A & id <= rot B` means "if A has a cycle, so does B" (a necessary
  consequence of the rotation claim; the oracle cannot see paths).
- `rot` without `& id` has no meaning: Kater rejects it unless the left-hand
  side relates events only to themselves (a predicate), whose pairs are all
  cycles.
- `total r` means that r is a strict total order on all events, as
  Proposition 3.12 of the Kater paper has it; Kater uses only its
  transitivity. `total` of anything but a relation is unsupported, as in
  Kater.
- `let rec` is a least fixpoint, computed by Kleene iteration; the inverse of
  a recursive relation is the inverse of that fixpoint.
- An automaton denotes the pairs (a, b) such that an accepting path reads a,
  ..., b; the oracle computes it as the least fixpoint of reachability over
  (state, event) pairs.

### Tools

    kater-oracle check [-n EVENTS] [-t SECONDS] [--refutable] FILE...

Kater's verdict on each assertion next to a counterexample search. A
counterexample to an assertion Kater proved is reported as `UNSOUND`, with
the graph. With `--refutable`, an assertion without a counterexample is an
error: for files of false claims Kater has to reject.

    kater-oracle audit [-n EVENTS]

Every fact the Theory states about the builtins: inclusions between relations,
predicates and whole letters (`Theory::isIncludedIn`), domains and codomains,
disjointness between predicates, the label pairs that do not compose, the relations treated
as eco, the per-location variants, and the built-in assumptions
(`fr;mo <= fr`, `po;po <= po`, `mo;mo <= mo`, `rf;fr <= mo`); and that no
event has two `alloc`, `free` or `retire` predecessors, as the exported code
reads one (`alloc_pos()` and the like).

    kater-oracle transforms [-n EVENTS] [--cases N] [--seed S] [--depth D] [--only PASS]

Each automaton pass against its contract (below), on the automata of random
expressions.

    kater-oracle export [-n EVENTS] [--json DIR] FILE...

Exports FILE into a scratch directory and checks what the export relies on:
every claim the Checker proves on the way (recorded with
`Checker::setObserver`), the inclusion its extensibility check decides (see
[Extensibility](#extensibility)), the certificates of all of them, and that
every definition the exporter rewrites keeps its meaning. With `--json`, also
writes the certificates to DIR, as `certify` does.

    kater-oracle certify [-n EVENTS] [--json DIR] FILE...

Has Kater prove FILE's assertions with certificates
(`Checker::setCertificateSink`), checks each certificate without searching
(below), and checks every letter inclusion the certificates rest on against
the semantics. With `--json`, also writes the certificates to DIR for the
checker in Lean (below).

    kater-oracle explain FILE...

The left-hand automaton of each assertion through the stages of the inclusion
check, for triage.

    kater-oracle genmc --runner RUNNER [-n EVENTS] [--threads T] [--locations L]
                       [--heap-events H] [--random N] [--random-events M]
                       [--seed S] [--shard K/N] [--all-races]
                       [--graph FILE]... FILE...

Runs the GenMC checker Kater exports for each `kat/NAME-genmc.kat` FILE, inside
GenMC, on every graph up to EVENTS events, every one with a heap up to H, and
on N random ones, and compares its answers with the reference semantics (see
[The exported checkers](#the-exported-checkers)).

    kater-oracle extensible [-n EVENTS] [--threads T] [--locations L]
                            [--graph FILE]... [--refutable] FILE...

Checks that the model of each `kat/NAME-genmc.kat` FILE is extensible, on every
graph up to EVENTS events, or on the graphs of FILEs: that an event GenMC may
add to a consistent graph can be added consistently (see
[Extensibility](#extensibility)). With `--refutable`, the models are expected
not to be.

    tests/oracle/fuzz.py [--cases N] [--jobs J] [--seed S] [--profile P]

Random files with one assertion and a few assumptions; the right-hand side
is a random weakening of the left-hand side, mixing sound steps (`rfe` to
`rf`, adding alternatives) with unsound ones (`po` to `po-loc`, `ATOM` to
`ACQ`). Every assertion Kater proves goes to `kater-oracle check`. Profiles
add compilation schemes (`comp`), dependencies (`deps`), `total`, odd
assumption shapes (`shapes`) and `let rec` definitions (`rec`). Findings are kept
as `.kat` files.

The ctests labeled `oracle` (built when Z3 is found) run the audit, the
transformation contracts, the correct suite against counterexamples and with
certificates, the soundness regressions with `--refutable`, the export check
and the extensibility of every `kat/*-genmc.kat` model, and the two models of
`tests/oracle/extensible`, which are not extensible; when `lake` is found too,
the ones labeled `formal` check the certificates of the suite and of the
exports with the checker in Lean, and with GenMC (below), the ones labeled
`genmc` run the exported checkers:

    ctest -L oracle

## The contracts of the decision procedure

Kater decides `A <= B` by translating both sides to automata, normalizing
them, saturating the left-hand side for `& id` and the right-hand side with
the hypotheses, and checking that every word of the left automaton is matched
letter by letter by a word of the right one, where a letter is matched by any
label the Theory says includes it. The verdict is sound if each step meets its
contract, on every graph satisfying the hypotheses H:

| Pass | Contract |
|------|----------|
| `RegExp::toNFA` | `[[toNFA(e)]] = [[e]]` |
| `normalize`, `simplify`, `compactEdges`, `breakToParts`, `removeConsecutivePredicates`, `addTransitivePredicateEdges`, `removeDeadStates`, `removeSimilarTransitions`, `removeRedundantSelfLoops`, `saturateDomains`, `to_DFA` | preserve the denoted relation |
| `saturateInitFinalPreds`, `saturateLoc` (left-hand side of `& id`) | keep every cycle: `[[T(N)]] & id ⊇ [[N]] & id` |
| `saturateRotate` (right-hand side of `rot`) | add no cycle |
| `saturateEmpty`, `saturateID`, `saturateTransitive`, `saturateBuiltin`, `saturateSubword` (right-hand side) | under H, `[[T(N)]] ⊆ [[N]]` |
| `pruneNFA` (right-hand side) | removes transitions: `[[T(N)]] ⊆ [[N]]` |
| `Theory::isIncludedIn`, `composes` | true of every graph (the audit) |
| letter-wise matching | a matched word's relation is within the matching word's |

`kater-oracle transforms` tests these rows directly: the right-hand-side
saturations under their hypotheses (`[[A]] = 0` for `saturateEmpty`,
`[[A]] <= id`, `r;r <= r`, `[[A]] <= r`, `[[A]] <= [[w]]`), the others
unconditionally.

### Certificates

When the final check succeeds, `Checker` can hand out a certificate: the two
automata, the simulation it used on the left one, the pairs (left state, set
of right states) it explored, and the letter inclusions the theory answered.
`kater-oracle certify` checks, without searching, that

1. the simulation is reflexive, transitive, and a simulation: a simulator
   accepts where the simulated state does, and follows each of its steps;
2. a pair covers each starting state: some pair (s, Q) has s simulating the
   start and Q within the right automaton's starting states;
3. each pair whose left state accepts has an accepting right state;
4. each step p --a--> p' out of a pair (p, P) lands on a pair the simulation
   subsumes: some (s, Q) with s simulating p' and Q within the states P
   reaches by the letters a is included in.

By induction over a word of the left automaton, a pair subsumes its run at
every step, so (3) makes the word accepted by the right automaton letter by
letter. Together with the letter inclusions, which the oracle checks, the
certificate proves the inclusion between the two automata. What it leaves to
trust is how those automata came from the expressions: the contracts above.

### The checker in Lean

`formal/` is a Lean 4 project, depending on nothing but Lean's core library,
that proves a checker of these certificates sound. It models what a
certificate is about, as the oracle reads it:

- relations on a type of events, and a meaning for the base relations and
  predicates by id: an execution graph, in the sense of §2.3 of the Kater
  paper, with the builtins uninterpreted;
- a letter (`TransLabel`) as `[pre];r;[post]`, or `[pre]`, which is within
  the identity, where predicates may be complemented and relations inverted;
- a word as the composition of its letters (the identity if it is empty),
  and an automaton as the pairs of events that a word it accepts from a
  starting state relates.

`Certificate.check` (`formal/KaterCert/Checker.lean`) is `checkCertificate`
in Lean: the same conditions, in the same order, with the same messages.
`lake build` proves it sound (`formal/KaterCert/Soundness.lean`):

```lean
theorem check_sound (c : Certificate) (h : c.check = none)
    (I : Label → Rel E) (hinc : ∀ a b, (a, b) ∈ c.inclusions → Rel.Sub (I a) (I b)) :
    Rel.Sub (c.lhs.denote I) (c.rhs.denote I)
```

If the checker accepts a certificate, and each of its letter inclusions holds
when letters mean `I`, then so does the inclusion between its automata;
`check_sound_interp` states it for letters read as above, over any meaning of
the base relations and predicates. The proof is the induction above, on the
four conditions over any automata (`formal/KaterCert/Conditions.lean`). It
has no `sorry` and uses only Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): the build checks this and fails otherwise.

The proof needs less than the checkers check. That a simulator accepts every
word of a state it simulates follows from (1) for that pair alone, by
induction over the word, and a state needs no simulation to accept its own
words; so neither reflexivity nor transitivity is used. To the proof, a
negated predicate is a letter like any other. Both checkers keep these
conditions, so that they agree.

`kater-oracle certify --json DIR` writes each certificate to DIR with
`checkCertificate`'s verdict, along with copies that each differ from it in
one place (a pair dropped or shrunk, an entry of the simulation flipped, an
inclusion dropped, the right automaton accepting nothing, ...), each with
`checkCertificate`'s verdict on the copy. `kater-cert-check` reads the files,
checks them, and compares the verdicts:

    Release/kater-oracle certify -n 1 --json /tmp/certificates tests/correct/*/*.kat
    cd formal && lake exe kater-cert-check /tmp/certificates

On `tests/correct`, it accepts the 54 certificates, and gives each of the 637
copies the verdict `checkCertificate` gives it, reason included, in about
three seconds. 57 copies are still valid proofs: most replace the simulation
with the identity (36) or drop a right state from a pair (11), neither of
which those proofs need, and 7 make the right automaton accept nothing where
the left one accepts nothing either.

What a verdict of the final check now rests on: the letter inclusions, which
stay hypotheses (the oracle checks them up to N events); the C++ that writes
the certificates and the Lean that reads them, since the theorem is about the
automata in the file; and Lean's kernel and compiler. What the automata mean
for the expressions rests on the contracts above.

The Lean has to stay in step with the C++ it mirrors. Comparing the verdicts
catches a checker or a format that drifts, but not a model that does: a field
added to `TransLabel`, say, that the JSON leaves out would make two letters
the same in Lean and different in Kater. So the C++ that the Lean mirrors is
marked, region by region, with comments that name the Lean mirroring it
(`/* formal: begin TransLabel, mirrored by formal/KaterCert/Label.lean */`
... `/* formal: end TransLabel */`): the letters, their comparison and their
meaning in the oracle, the meaning of automata, `Checker::Certificate`,
`checkCertificate`, and the JSON writer. `formal/mirrors.txt` records a
SHA-256 of each region, without whitespace, as of the last review of the
Lean against it. `scripts/check-mirrors.sh` (the ctest `check-mirrors`,
labeled `lint`) reports each region that changed since, with the Lean to
review; after the review, `scripts/check-mirrors.sh --update` records the
regions as they are.

## The exported checkers

`kater-oracle export` checks what the exporter proves and rewrites; the code
`GenMCPrinter` prints from that has to be run. `kater-oracle genmc` runs it: it
hands small graphs to the checker Kater exports for a model, inside GenMC, and
compares the checker's answers with the model's meaning in the reference
semantics.

Kater and GenMC both define a global `Config`, a `VSet` template and the same
error macros, so they cannot share a translation unit, nor safely a link. The
checker runs in a process of its own, `kater-oracle-runner MODEL`, which links
GenMC's core library and the six exported checkers (exported by the build as
`ORACLE<MODEL>Checker`) and nothing of Kater. It reads a graph and queries from
a pipe, builds GenMC's execution graph, calls the checker, and writes the
answers back; `kater-oracle genmc` works out the reference's answers and
compares. A runner that crashes, or takes over a minute on a graph, is
restarted, and the graph reported.

A graph is an `Execution` (`tests/oracle/Execution.hpp`): events with a kind,
an ordering, a location and the class of their GenMC label (LKMM's fences,
locks, SRCU accesses, fully ordered and non-returning RMWs, failed
compare-and-swaps), the hazard pointer of a protection, and the edges `rf`,
`mo`, the dependencies, `tc`, `tj` and `lin`; a location an allocation is of
is a heap block. The reference is the oracle's semantics as it stands: `Graph`
has a concrete mode, in which every unknown is a constant, so every formula
over the graph folds to one, and the code that gives `.kat` its meaning for
the solver gives it on the single graph. (`Term` keeps a constant as a plain
truth value and makes it a solver term only on demand, which made this six
times faster.)

### From a graph to GenMC's

The runner adds the events to an `ExecutionGraph` (a `DepExecutionGraph` for
IMM and LKMM) as GenMC's driver does: each after its `po`, `rf`, `tc`, `tj` and
`lin` predecessors (`Execution::additionOrder`), a read with its `rf`, a write
put in `co` after the writes before it there, then `updateMMViews`. The first
thread starts with GenMC's initial label, every other thread with a thread
start. An RMW is a `FaiRead` and a `FaiWrite` (`NoRetFai*` and `LockCas*` for
LKMM), a failed compare-and-swap a `CasRead` expecting a value no write writes.
`lin` is added last, as Relinche adds it to a complete graph. A graph with a
porf cycle, which only IMM and LKMM build, has every event added before any
`rf` or `co`, and its views computed again until they settle.

An allocation is a `MallocLabel` of a heap block, which the runner allocates
in GenMC's `ExecutionState` (`onAlloc()`); a free is a `FreeLabel`, a retire
an `HpRetireLabel`, a protection an `HpProtectLabel` through a hazard pointer
of a static location that nothing else accesses. The state records each event
once it is added, with the views it has then (`onNALoad()`, `onATStore()`,
`onFree()`, `onProtect()`, ...), as `reconstructState()` rebuilds it on a
restart. For the memory-error checks, the runner adds every event as
`GenMCDriver` does: its views, a write's place in `co`, then, for a read, a
write, a free or a retire, `checkErrors()` and `checkWarnings()`
(`checkForRaces()`), before a read's `rf`, which comes next with its views
again. An error stops the execution.

The graphs are those GenMC builds: they satisfy the oracle's axioms, their
RMWs are atomic (in `co`, an RMW's write comes right after the write its read
reads), and they have no cycle of `po | rf | tc | tj | lin` (for IMM and LKMM,
of GenMC's prefix relation, `(ppo | rfe | tc | tj | lin)+`). For a graph with
`lin`, that is the graph without it: Relinche adds `lin` to a graph GenMC
built, whatever cycles it closes. Dependencies come from reads, and go to the
events GenMC records them for (not thread starts, method calls, or the write
of an RMW). A block's allocation precedes its events in porf.

### What is compared

| Check | GenMC | The reference |
|-------|-------|---------------|
| `consistent` | `isConsistent(G)` | every `acyclic` and inclusion export holds (not its `unless` clause, which the full check ignores) |
| `incremental` | `isConsistent(e)`, `e` added last as GenMC adds it: its views, then its `rf` or `co` | every export holds or its `unless` clause does; where `G \ e` satisfies the exports |
| `view` | each view of each event | the event and its predecessors in the view's definition; on graphs without a porf cycle |
| `prefix` | `calculatePrefixView(e)` | `e` and its `(ppo \| rfe \| tc \| tj \| lin)+` predecessors (`KatModule::createPPORF`) |
| `rprefix` | `calculateRevisitPrefixView(e)` (LKMM) | the same with `rppo` |
| `stores` | `getCoherentStores(r)`, `r` added last, without its `rf` | the writes, and the initial value, `r` can read from with `G` coherent; where `G \ r` is coherent |
| `placings` | `getCoherentPlacings(w)`, `w` added last, not in `co` | the places in `co` that leave `G` coherent and RMWs atomic |
| `revisits` | `filterCoherentRevisits(w, reads)`, `w` added last (SC, TSO, RA, RC11) | the reads outside `w`'s prefix whose revisit by `w` leaves a coherent graph: the events added up to the read, and `w`'s prefix, with the read reading from `w` |
| `relinche` | `isCoherentRelinche(G)`, on graphs with `lin` | `G` is coherent; where it is without `lin` |
| `clause` | each `export error` and `export warning` clause (`checkErrorN`, `checkWarningN`, called by a checker of their own) at each event GenMC checks, the events added as `GenMCDriver` adds them, with each event that can be last, last, up to the first error | its `unless` clause, `A <= B`, holds at the event `e`: every `A`-predecessor of `e` is a `B`-predecessor, on the graph as GenMC has it then: the events before `e` in the execution state, and `e` without its `rf` |
| `errors` | `checkErrors(e)` at the same events | the error of the first error clause that fails, with a race among the events that refute it |
| `warnings` | `checkWarnings(e)`, with no warning reported yet | the warnings of the warning clauses that fail, in order, each with such a race |

`G` is coherent when the view `export coherence` names, composed with
`(rf | mo | fr)+`, is irreflexive. LKMM's user predicates mean what the GenMC
code `kat/lkmm-genmc.kat` gives them does, on the labels the runner makes;
`prop-int`, which GenMC computes by hand (`prop_int_preds`), is
`(prop \ id) & int`.

An exported clause checks the pairs that end at the event just added, with
the positional relations read from the state: that is all GenMC asks, and
what the reference evaluates, its positional builtins being relative to the
state (see [Execution graphs](#execution-graphs)). The checks run once for
each event that can be added last, so each event is checked with the others
in several orders: the order of the state decides the last NA write of a
location, the last free of a block, and whether an access was protected.
`A = B` (none of the models has one) holds at `e` in both directions, and an
export without `unless` never does. The build has the checker's clauses as
`ORACLE<MODEL>Clauses` (`tests/oracle/genmc/Clauses.cmake`), as they are
protected members of their own names.

The graphs are every one up to a number of events (thread starts aside),
threads and locations, over instructions that tell apart what the model does:
SC's `na` and `sc` accesses; TSO's, RA's and RC11's orderings; RMWs and fences;
for IMM and LKMM, a dependency on the read before an event; for LKMM its twelve
kinds of fence, locks and unlocks, SRCU, and its RMWs. Then, for the
memory-error checks, every graph up to `--heap-events` events over
allocations, frees, retires, protections through one hazard pointer, plain
accesses and atomic ones of the orderings the model's hb tells apart (SC's
`sc`; `rlx`, `acq` and `rel` for the others), but those of the model's own
instructions: the graphs with a heap, and, for TSO and RA, whose instructions
have no plain accesses, those with a plain access. And random graphs of up
to `--random-events` events, with thread creation and joins, method calls and
`lin`, each of a few instruction kinds or of one ordering: half of them built
as GenMC builds a graph (events in a random interleaving, each read reading
from a write, and each write going in `co`, where the graph so far stays
coherent), half anything the axioms allow. Half of each have frees, retires
and protections through two hazard pointers too, and plain accesses for TSO
and RA: the locations they are of, and others at random, are heap blocks,
allocated at the start of the first thread with an event of them (the graphs
where porf reaches the block's other events).

The ctests labeled `genmc`, one per model, are built when `GENMC_SOURCE_DIR`
(a CMake variable, or the environment variable when configuring) names a GenMC
source tree; the build makes its core library without LLVM. Each takes one or
two minutes:

    cmake -DGENMC_SOURCE_DIR=PATH/TO/genmc BUILD-DIR
    ctest -L genmc

### Results

Every graph up to the bound (3 threads, 2 locations) and random ones (up to
8 events, 4 threads, 3 locations); each cell is how many times the check
ran and, in parentheses, how often the answer was false or ruled some choice
out:

| | SC | TSO | RA | RC11 | IMM | LKMM |
|---|---|---|---|---|---|---|
| every graph up to | 5 events: 1484510 | 4: 408207 | 4: 87326 | 4: 1278894 | 4: 7221304 | 3: 367790 |
| random graphs | 120000 | 120000 | 120000 | 120000 | 120000 | 220000 |
| `isConsistent(G)` | 1604510 (188065) | 528207 (21010) | 207326 (0) | 1398894 (1866) | 7327628 (12243) | 584876 (1444) |
| `isConsistent(e)` | 3315120 (135646) | 1049745 (15734) | 364813 (0) | 2945257 (1050) | 11817659 (9231) | 858382 (1149) |
| views | 32.5M | 9.6M | 4.4M | 23.8M | 107.7M | 6.1M |
| prefixes | 10.8M | 3.2M | 1.5M | 7.9M | 35.9M | 3.0M, and 3.0M of `rppo` |
| `getCoherentStores` | 1504384 (398355) | 406224 (67204) | 106150 (17446) | 1191333 (201659) | 4794766 (1004208) | 241837 (27883) |
| `getCoherentPlacings` | 1544086 (420656) | 443883 (78190) | 162285 (26347) | 1252985 (214478) | 4876791 (1021195) | 259435 (30301) |
| `filterCoherentRevisits` | 675549 (65105) | 141925 (8647) | 36711 (2227) | 431477 (26148) | | |
| `isCoherentRelinche` | 8223 (521) | 8290 (377) | 7598 (334) | 8002 (389) | 9250 (1317) | 18016 (1756) |
| disagreements | 0 | 0 | 0 | 0 | 0 | 0 |

(RA's consistency is coherence alone: its `isConsistent` is always true.)
These are the checkers since item 16, whose acyclicity checks run Tarjan's
algorithm. Before it, the same comparison found a bug,
[#27](https://github.com/vzhn/kater-fork/issues/27): graphs of IMM whose
method calls `lin` orders in a circle, so that `hb` and then `psc` have a
cycle, which the full `isConsistent(G)` missed, depending on the order it
explored the labels in (renumbering the threads of the smallest made it find
the cycle). Of the random graphs of IMM above, the checker from before item
16 accepts 22 of 120000 that way; the one from after accepts none. The ctest
`oracle-genmc-issue-27` replays the smallest such graph,
`tests/oracle/genmc/graphs/issue-27.graph`.

The memory-error checks came later. They ran on every graph up to the bounds
above, but IMM's (3 events), every graph of their own instructions up to 5
events (TSO and RA: 4), and 100000 random graphs per model, half of them with
a heap; each cell is how many times the check ran and, in parentheses, how
often the clause failed, or GenMC found an error or a warning:

| | SC | TSO | RA | RC11 | IMM | LKMM |
|---|---|---|---|---|---|---|
| every graph up to | 5 events: 1484510 | 4: 408207 | 4: 87326 | 4: 1278894 | 3: 66901 | 3: 367790 |
| and of the memory-error checks | 5 events: 221273 | 4: 209950 | 4: 209950 | 5: 964818 | 5: 967572 | 5: 967572 |
| random graphs | 100000 | 100000 | 100000 | 100000 | 100000 | 100000 |
| clauses | 103.4M (3.7M) | 39.9M (0.9M) | 21.2M (0.5M) | 121.6M (3.9M) | 55.2M (2.0M) | 45.2M (0.9M) |
| `checkErrors` | 12925529 (3191242) | 4991701 (354097) | 2650045 (355264) | 15201110 (2587297) | 6901743 (1408051) | 9043394 (194512) |
| `checkWarnings` | 9734287 (436589) | 4637604 (527426) | 2294781 (166484) | 12613813 (1098685) | 5493692 (436521) | 8848882 (683522) |
| disagreements | 0 | 0 | 0 | 0 | 0 | 0 |

The checks of the previous table ran again on these graphs, and agreed too:
the checker from before item 16 accepts 15 of these random graphs of IMM,
#27's, and the one from after none. Every clause of every model fails on
some graphs, in the ctests already: the memory-error clauses tens to
hundreds of times, the races thousands. Left out is the race of a failing clause `A = 0`, which the exported
checks do not set ([#34](https://github.com/vzhn/kater-fork/issues/34)):
compared (`--all-races`), it disagrees in 1074 of the 31817 errors GenMC finds
on RC11's graphs of the memory-error checks up to 4 events, where
`checkErrors()` gives the race of a double free, of a use after free or of an
access to a retired block as none, or as what an earlier failing clause left.
`tests/oracle/genmc/graphs/issue-34.graph` has a warning leave its race to a
double free; the ctest `oracle-genmc-issue-34` compares it with
`--all-races`, and fails once the bug is fixed.

Three differences are explained, and the comparison allows for them:

- A GenMC `View` is a vector clock whose entries default to index 0, so it
  always contains every thread's start: views and prefixes are compared
  without thread starts.
- The full `isConsistent(G)` ignores `unless` clauses and the incremental one
  honours them (`GenMCPrinter::output`). An `unless` clause excuses a cycle only
  in a coherent graph: `[SC];any;[SC] <= id` implies `acyclic psc` only when
  `hb;eco` is irreflexive. In an incoherent graph, removing one of two SC fences
  can leave a `psc` cycle that the clause then excuses, and that the
  incremental check from that fence, which looks for cycles through it, cannot
  see. GenMC builds only coherent graphs, and keeps the constraints themselves
  before it adds an event; so does the comparison.
- The printed prefix of the models without dependency tracking
  (`calcPPoRfBefore`) follows `po`, `rf`, `tc` and `tj`, not `lin`, which
  `createPPORF` has. GenMC adds `lin` only when Relinche checks a complete
  graph, after every prefix is computed, so the difference cannot show; views
  and prefixes are compared on graphs without `lin`.

Not covered:

- Revisits under IMM and LKMM, whose revisited graph has holes, and the
  reads-from of the reads in it (`GenMCDriver::getRevisitView`), which is
  GenMC's driver more than the checker; and reads added before events a revisit
  kept, which GenMC's LKMM mode relocates.
- The memory-error checks of graphs with a porf cycle (IMM, LKMM), whose state
  GenMC rebuilds in an order of its own (`reconstructState()`).
- A read GenMC records in its state as it adds it, with the views it has
  before its `rf` (`handleLoad()`); the runner records it with its `rf`, as a
  restart does. The last accesses of a location then differ only by accesses
  `hb`-before another one kept, which the checks `... <= hb` cannot tell apart,
  though one may be the race reported.
- What GenMC's driver checks around the checker: invalid and uninitialized
  accesses (`checkAccessValidity()`, `checkInitializedMem()`), the WW race it
  reports from a write's placings in `co`, the warnings it reported in other
  executions (the runner tells the checker it reported none), and LKMM's races
  and frees, which it decides on complete executions (`checkLkmmRace()`,
  `checkLkmmSrcu()`).
- Hazard pointers written or freed, which ends their protection; blocks of
  more than one location.
- Labels the instructions do not make: abstract locks, helped
  compare-and-swaps, barriers, condition variables, thread kills; and GenMC's
  hand-written LKMM checks (RCU, plain accesses).

## Extensibility

GenMC explores a program by adding one event at a time to a consistent
graph, and relies on every addition having a consistent outcome: otherwise
an exploration stops at a graph whose completions it was meant to reach.
This is *extensibility* (Definition 5.4.1 of Kokologiannakis's thesis;
*maximal extensibility* in TruSt, POPL'22). GenMC adds an event once its
predecessors in its prefix relation, `pporf = (ppo | rfe | tc | tj | lin)+`
(`KatModule::createPPORF`), are in the graph. When `ppo` is `po` (SC, TSO, RA,
RC11), that event is the last of its thread and nothing follows it: added
reading from the last write in `mo`, or last in `mo`, it has no outgoing
edge, and closes no cycle of a model whose constraints use relations only
positively (§3.8 of the Kater paper). When `ppo` is not `po` (IMM, LKMM), a
revisit keeps the revisiting write's `pporf`-prefix and drops the events
`po`-before it that are not in it; GenMC adds those later, into the hole, and
such an event has `po`-successors already, to which the constraints may
relate it (HMC, ASPLOS'20, walks through one: in load buffering, the read of
the second thread is added after the write that follows it).

As a constraint on graphs:

> For every graph G that GenMC can build, and every event e of G that nothing
> follows in `pporf` and nothing reads from, and that is neither part of an
> RMW nor a thread start: if G without e is consistent, then G is, for some
> choice of where e reads from (if a read) or of e's place in `mo` (if a
> write).

Consistent means what the full `isConsistent` checks, with coherence: every
`acyclic` and inclusion export holds, and the view of `export coherence`
composed with `eco` is irreflexive. RMWs are left out: GenMC adds the write
of an RMW right after its read, and lets the graph be inconsistent for that
step when another RMW has read the same write (§5.5 of the thesis).

### What Kater checks

`Checker::isPPOIntersectionInPPO`, which the exporter calls for every
acyclicity export ("Check extensibility" in
`Exporter::checkExportRequirements`), is meant to establish this. It builds
the automaton of the starred constraint and cuts it at its `eco` steps (a
state with an incoming `eco` step is split from its other incoming steps, and
the sources of `eco` steps accept), drops the `eco` steps, and decides that
what is left, the stretches of the constraint's cycles between `eco` steps,
is within `(any* ; pporf ; any*) | id`. It goes through neither
`checkAssertion` nor the observer, and it prunes nothing: the exporter fails
the export when it does not hold, and uses it for nothing else.

It establishes nothing ([#33](https://github.com/vzhn/kater-fork/issues/33)).
It looks for the `eco` steps among the incoming transitions of states, whose
labels are inverted (`rf^-1`), which `Theory::isEco` does not count. So it
cuts nothing, its left automaton accepts no word, and the inclusion holds of
every acyclicity constraint, as it has since the check came in with v0.3.
With the labels turned around, it would still not establish extensibility:
its starting states leave out every state that an `eco` step can follow,
and even cut as meant, a `pporf` step somewhere in each stretch does not keep
the added event out of a cycle. `tests/oracle/extensible` has a model for
each case, `mp-genmc.kat` and `mp-acq-genmc.kat`: Kater exports both, and
neither is extensible (next to each, a graph where a write GenMC adds into a
hole closes a cycle in message passing).
With the labels turned around, IMM and LKMM would fail the check where the
theory does not know that a thread join or a lock read is an acquire, though
both are extensible on small graphs (below).

### What the oracle checks

- `kater-oracle export` records each extensibility check by its certificate:
  `isPPOIntersectionInPPO` hands its certificate to the certificate sink,
  with the acyclicity constraint, as `checkInclusion` does with the subset
  constraint it decides. The export check checks the certificate, the letter
  inclusions it rests on, and the inclusion between its two automata on
  every graph up to N events, and reports the check as `vacuous` when its
  left automaton accepts nothing: for all seven acyclicity exports of
  `kat/*-genmc.kat` (RA has none), today. With `--json`, it writes these
  certificates with the others; the checker in Lean accepts the 61
  certificates of the six exports (7 of them the extensibility checks'), and
  gives each of their 754 copies `checkCertificate`'s verdict.
- `kater-oracle extensible` checks the property itself on concrete graphs:
  every graph `kater-oracle genmc` enumerates (3 threads, 2 locations, thread
  events aside), each event in it GenMC may add, and every way of adding the
  event to the graph without it (each graph without the event is taken
  once, from the first of the graphs that add it, so that the cost stays
  that of the enumeration).

| | SC | TSO | RA | RC11 | IMM | LKMM |
|---|---|---|---|---|---|---|
| every graph up to 3 events | 2480 | 10533 | 3294 | 24769 | 66901 | 367790 |
| events added to a consistent graph | 3615 | 16128 | 4914 | 37992 | 97447 | 684992 |
| of which into a hole | 0 | 0 | 0 | 0 | 10915 | 198645 |
| that cannot be added consistently | 0 | 0 | 0 | 0 | 0 | 0 |

The six models are extensible on these graphs; at 3 events, LKMM takes ten
minutes, IMM 40 seconds. The two of `tests/oracle/extensible` are not: each
at its graph, and `mp-genmc.kat` at 1024 events of the graphs up to 4 events
and 2 threads. The ctests `oracle-extensible` (up to 3 events) and
`oracle-extensible-lkmm` (up to 2) check the six models,
`oracle-extensible-refuted-*` the two others at their graphs; and
`oracle-export-issue-33-*` pass while Kater exports the two models, and fail
once it rejects them.

## Findings

All fixed, with a regression test each. Most were found by the oracle, the
others by running Kater under sanitizers or with assertions, by type-checking
exported checkers, and by reading the code. The files in `tests/wrong/soundness` are false claims
Kater used to prove; the oracle refutes each (`ctest -L oracle`).

1. **Dependencies and `po-imm` were in `po-loc`** (`Theory::isIncludedIn`;
   fixed in "Theory: dependencies and po-imm are not in po-loc, po-loc-imm not
   in po-imm"). The rule for relations within a thread put all of them in
   `po-loc` as well as `po`, so Kater proved `ctrl <= po-loc`,
   `addr <= po-loc`, `data <= po-loc` and `pctrl <= po-loc`. The per-location
   rule made `po-loc-imm` a subset of `po-imm`, which it is not in GenMC. The
   audit found these five facts (11 with their inverses) among 2108 that hold.
   No exported checker changes.

2. **Compilation schemes were saturated as an empty set** ("Compilation
   schemes: saturate with the scheme's shortcut, not an empty set"). An
   assumption `[A];po;[B] <= [A];po;[C];po;[B]` added
   `any*;[A];(po;[~C])*;po;[B];any*` to the right-hand side, as if
   `[A];(po;[~C])*;po;[B]` were empty. It is not, since `po` steps over
   events, so Kater proved `[R];po;[W] <= 0` from
   `[R];po;[W] <= [R];po;[F];po;[W]` (R; F; W in one thread refutes it). The
   TSO compilation proofs in `tests/correct/compilation` used this step. Their
   theorems hold (no counterexample with up to 5 events) and are now proved
   soundly: wherever the right-hand side reads `[A];po;[C];po;[B]`, it may
   read `[A];po+;[B]`, the same relation as `[A];po;[B]`.

3. **`saturateInitFinalPreds` dropped words** ("saturateInitFinalPreds: keep
   the words it cannot merge"). For `& id` it removed every final predicate
   and added back only the ones merged with an initial predicate. A word of a
   single predicate (`[R;ACQ] & id <= 0`, `(po | [R]) & id <= po`) had none,
   and a starting state with a loop into it had its predicates taken for first
   letters (`((po-loc)*;[R];u0^-1;[UW]) & id <= moi^-1`). Kater proved all
   three; the fuzzer found 15 such cases in 7300 before the contract test
   pinned the pass down.

4. **`saturateLoc` dropped the inversion** ("saturateLoc: replace a relation
   with its variant in the same direction"). It replaced `po^-1` with
   `po-loc`, so Kater proved `(mo;po^-1;fr) & id <= mo;po-loc;fr`, refuted by
   a coherence-style cycle of three events.

5. **An assumption `A <= [P]` read an empty `std::optional`** ("Assumptions:
   read `A <= [P]` as `A <= id`"): undefined behaviour. It is now saturated as
   `A <= id`.

6. **The GenMC code of `RLX` and `LOC` did not compile** ("Builtins: GenMC
   code for RLX and LOC that compiles"): `isRelaxed()` does not exist in GenMC,
   and `LOC` lacked a `>`. No shipped model checked either predicate. Found by
   type-checking exported checkers against GenMC's headers.

7. **Assumptions lost their `& id`** ("Assumptions: do not apply `A & id <= B`
   as `A <= B`"). Saturation and the theory read an assumption's two sides
   and ignored its flags, so `assume r & id <= 0` (r is irreflexive) was
   used as `r <= 0`, and Kater proved `r <= 0`. Such assumptions are now
   reported as unsupported, as the code's own FIXME had asked.

8. **`rot` without `& id`** ("Parser: rot needs & id on the left-hand
   side"). Rotating words that are not cycles let Kater prove
   `rf;po <= rot (po;rf)` and `po;[W];po <= rot (po;po;[W])`; the parser now
   rejects the form.

9. **Malformed assumptions crashed Kater or read empty optionals**
   ("Assumptions: `total` of anything but a relation is unsupported",
   "Assumptions: transitivity is of relations"): `assume total (po | rf)`
   segfaulted, and `assume total [R]`, `assume [R];[R] <= [R]` and
   `assume [R]+ <= [R]` read the relation of a predicate. Found by running
   Kater under ASan, UBSan and `_GLIBCXX_ASSERTIONS` on the test suite and on
   fuzzed assumptions.

10. **Every export dereferenced a null pointer** ("Statement: no null
    dereference for a missing unless or constraint"): `getUnless()` returned
    `&*unless_` for exports without an `unless` clause. It happened to yield
    `nullptr`; under `_GLIBCXX_ASSERTIONS` every export of every model aborted.

11. **The inclusion check split a letter into one case twice** ("Checker:
    split a letter into both of its cases"). When the right-hand side tests a
    negated predicate `~p`, each letter is checked with `~p` and with `p`; the
    second case merged `~p` again, so the case of `p` was never checked.
    Dormant since the fix of item 2, which removed the only source of negated
    predicates; until then it made compilation schemes skip the case of a
    fence. Found by reading the code; a unit test covers it.

12. **A predicate letter was within relation letters** ("Theory: a predicate
    letter is not within a relation letter"): `isIncludedIn` held `[R] <= po`,
    since it compared only the checks when the first letter had no relation.
    The alternation of predicate and relation letters in normal forms kept the
    inclusion check from using it. Found by checking the letter inclusions the
    certificates record.

13. **`total r` made r reflexive** ("Assumptions: total r gives r's
    transitivity, not a preorder"; #19). `saturateTotal` made every r-step of
    the right-hand side optional as well as repeatable, as if r were a
    preorder, so Kater proved `id <= r` from `assume total r`, `[W] <= mo` from
    `assume total mo`, and the cycle query `((x;y) & id) <= rot (x;r;y)`, the
    kind the saturation was meant for. Under a strict total order, its
    contract failed on 2 of 300 random expressions. `total r` is now
    saturated as `r;r <= r` is, and the oracle gives it its meaning.

14. **`addTransitivePredicateEdges` lost paths through three predicates**
    ("addTransitivePredicateEdges: compute the shortcuts before adding any";
    #20). It added a state's shortcuts as soon as it visited the state, so a
    state visited later took them for second steps of its own and removed
    them: through `0 -[]-> 2 -[ACQ&F]-> 16 -[]-> 18`, with `4 -[]-> 2`, the
    word `[ACQ&F]` from 0 was lost. It did not show through `normalize`. The
    contract tests now run both predicate passes on automata straight from
    `toNFA`, where they found 5 violations in 1200 expressions before the fix
    and none since; a unit test has the automaton above.

15. **Normalization never ended on a cycle of predicates** ("compactEdges:
    stop when a round changes nothing"; #22, #28). `joinPredicateEdges`
    reported a change whenever it removed a step, even one it added back, so
    through a cycle of predicates between states that do not accept,
    `compactEdges` looped forever. Assumptions that make a relation reflexive
    or within `id`, such as `assume data = [EXCL]`, make such cycles, and so
    does `(id | [EXCL] | [R])+`. The four files that took Kater over 30
    seconds were this, not a large automaton; they now take about 10 ms, as
    does `(id | [EXCL] | [R])+ <= id | [EXCL] | [R]`.

16. **The exported acyclicity checks could miss a cycle** ("GenMCPrinter: find
    the cycles of acyclicity checks with Tarjan's algorithm"; #27). The search
    `GenMCPrinter` prints for `acyclic` runs over (automaton state, label)
    pairs, and a cycle counts when it passes through the automaton's starting
    state, which every iteration of the relation does. The search took a pair
    off its stack once it had explored it and never explored it again, and the
    full check kept these marks across the labels it starts from: a pair
    finished while no starting pair was on the stack hid every cycle through
    it from a starting pair entered later. IMM's `isConsistent(G)` accepted
    graphs whose `lin` orders method calls in a circle, depending on the order
    of the threads. The search is now Tarjan's algorithm: a pair stays on the
    stack until its strongly connected component is complete, and an edge to a
    pair on the stack closes a cycle through the starting state exactly when a
    pair of that state is at or above it on the stack, since all those pairs
    are in the edge's component. Found by `kater-oracle genmc` (see
    [Results](#results)). On graphs of 100 to 400 events the checks take up
    to 11% more cycles (RC11, and IMM 6.5%; SC, TSO and LKMM within 1.5%).

17. **With assertions on, every export aborted** ("GenMCPrinter: a traversal
    may be of an automaton without states"; #35). `outputTraversal` asserted
    that an automaton has states, and the `0` of an error clause such as
    `free; [FREE|HPRET] = 0` has none, so a Kater built without `NDEBUG`
    aborted on all six `kat/*-genmc.kat` models. It now asserts what the
    traversal relies on, a visit entry for each state; a Release build, which
    prints the traversal of such an automaton for nothing to start, exports
    the same checkers as before. Found by building Kater in Debug to check the
    assertion of item 16; the ctests `export-*-genmc` export every model.

Items 1–4, 7, 8, 11 and 13 made Kater prove false claims, 12 and 14 could
have, 15 made it run forever, and 16 made an exported checker accept graphs
its model forbids; the others crashed it, read memory it should not, or
produced code GenMC rejects.
Under the sanitizers the whole suite, the unit tests, 4000 fuzzed files and the
export of every `kat/*-genmc.kat` model now run without a report, and the
exported checkers are the same as without them.

After the fixes:

- the audit finds no false fact (2108 hold, up to 4 events; 2960 with the
  inclusions between whole letters, up to 3);
- the transformation contracts hold on random expressions: over 1000 at
  depth 3 and 1600 at depth 4 for every pass, up to 4 events (the predicate
  passes on automata straight from `toNFA`: 2200 at depth 3 and 1000 at
  depth 4);
- the fuzzer finds no unsound proof in 25500 files, of which Kater proved
  8521, across all profiles; after items 13–15, none in 4500 more, of
  which Kater proved 1476 and never timed out (the oracle checked all but the
  64 that assume `total` of a compound expression, which Kater ignores);
- every assertion of `tests/correct` has no counterexample with up to 5
  events, and every proof of it has a valid certificate (54, resting on 498
  letter inclusions that hold);
- the export of every `kat/*-genmc.kat` model passes: 222 claims and
  rewrites with up to 5 events (7 of them the extensibility checks, which
  are vacuous), and 488 letter inclusions of the claims' certificates;
- every model is extensible on every graph up to 3 events (see
  [Extensibility](#extensibility));
- the exported checkers of all six models type-check against GenMC
  (0.19.0-vzhn.10), and the fixes left them byte-identical but for item 16,
  which changed their acyclicity checks alone; a Kater built with assertions
  exports the same ones;
- run inside GenMC, they answer as the reference semantics does on every
  graph tried, their memory-error checks included, but for the races of
  [#34](https://github.com/vzhn/kater-fork/issues/34), still open (see
  [Results](#results)).

## Open issues

- **Incompleteness.** `tests/wrong/equivalence/eq-ra1-ra2-no-universe.kat`
  has no counterexample with up to 5 events: it is probably true, but outside
  what Kater can prove. The four files of `tests/wrong/compilation` have none
  with up to 6 events either; two of them state assumptions Kater ignores
  (`po?;[R] <= [F];po;[R]` even rules out reads), and the two compilations of
  C11 to POWER either need larger graphs or are true once the right-hand
  sides exclude the uninteresting counterexamples they do.
- **Inverses of recursive relations.** `x^-1` for a `let rec x` flips the
  definitions in place, and Kater's automaton construction does not recognize
  the flipped self-reference `x^-1` as the recursion: it treats it as an
  unknown relation. That is sound (what holds for every relation in its place
  holds for `x^-1`) but incomplete: Kater cannot prove that the inverse of
  `let rec x = po | x;rf` is within `(po^-1 | rf^-1)+`.
- **Normal forms that keep predicate steps.** When a cycle of predicates
  stops `compactEdges` at a fixpoint (item 15), the predicate steps into
  states that do not accept stay in the normal form. That is sound; whether
  it costs completeness is untested. Kater rejects all four files of item
  15: the oracle refutes two, and finds no counterexample to the other two
  with up to 4 events (one has hypotheses no graph meets, since it makes
  `ctrl` reflexive, which Kater cannot know is impossible).
- **The race of an error whose `unless` clause is `A = 0`**
  ([#34](https://github.com/vzhn/kater-fork/issues/34)): the check
  `GenMCPrinter` prints for it sets no counterexample, so `checkErrors()`
  gives as the race of a double free or a use after free what an earlier
  failing clause left, possibly of an earlier execution, or none.
  `GenMCDriver::reportError()` dereferences it. Found by `kater-oracle genmc`;
  `tests/oracle/genmc/graphs/issue-34.graph` is the reproducer, and the ctest
  `oracle-genmc-issue-34` fails once this is fixed.
- **The exporter's extensibility check decides nothing**
  ([#33](https://github.com/vzhn/kater-fork/issues/33)):
  `isPPOIntersectionInPPO` looks for `eco` steps in inverted labels, finds
  none, and holds of every model, since v0.3; turned around, it would still
  accept models that are not extensible (see [Extensibility](#extensibility)).
  `tests/oracle/extensible` has two that Kater exports; the ctests
  `oracle-export-issue-33-*` fail once Kater rejects them. What the check
  should decide is open: a condition that implies extensibility, which
  `kater-oracle extensible` can test it against.
- **Not checked by the oracle**: of the printed code, the revisits of the
  dependency-tracking models (see
  [The exported checkers](#the-exported-checkers)).
- The oracle trusts Z3, its own axioms, and Kater's parser, which it shares.

## Next steps

1. **Certificates.** Kater emits certificates of its final step, and a
   checker proved sound in Lean checks them (see
   [The checker in Lean](#the-checker-in-lean)). What remains is
   certificates for the steps before: the passes, which could either be
   proved once from their contracts or emit evidence of their own (the
   saturations, for instance, which paths they added for which hypothesis).
2. **Formalization.** The model above is the specification: graphs and their
   axioms, the meaning of the builtins, of expressions and of automata. The
   contracts of the passes and the audit's facts are the lemmas. The oracle's
   counterexamples fix the corner cases a formalization must get right (the
   initial writes, `po-loc-imm`, same-location for non-accesses).
