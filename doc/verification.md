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
event has a kind, an ordering, and a few label flags; reads and writes have a
location. The base relations are `rf`, `mo`, the dependencies, `tc`, `tj` and
`lin`; everything else is derived.

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

Initial writes are implicit: a read of the initial value has no `rf` edge and
is `fr`-before every write to its location.

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

`same-thread`, `si`, `alloc`, `free`, `retire`, `loc-overlap`, `last_*` and
`unprotected` have no meaning in the oracle; constraints that use them are
reported as unsupported. User relations and predicates are uninterpreted,
subject to the module's `assume` and `disjoint` statements. The per-location
variant `r-loc` of a user relation `r` is `r & loc`.

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
(`fr;mo <= fr`, `po;po <= po`, `mo;mo <= mo`, `rf;fr <= mo`).

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
                       [--random N] [--random-events M] [--seed S] [--shard K/N]
                       [--graph FILE]... FILE...

Runs the GenMC checker Kater exports for each `kat/NAME-genmc.kat` FILE, inside
GenMC, on every graph up to EVENTS events and on N random ones, and compares its
answers with the reference semantics (see
[The exported checkers](#the-exported-checkers)).

    kater-oracle extensible [-n EVENTS] [--threads T] [--locations L]
                            [--graph FILE]... [--maximal] [--refutable] FILE...

Checks that the model of each `kat/NAME-genmc.kat` FILE is extensible, on every
graph up to EVENTS events, or on the graphs of FILEs: that an event GenMC may
add to a consistent graph can be added consistently (see
[Extensibility](#extensibility)). It counts as well the events, of these,
that nothing after them accesses the location of and that cannot be added
maximally, which Kater's extensibility check claims there are none of; with
`--maximal`, they decide the verdict too. With `--refutable`, the models are
expected not to be.

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
and the extensibility of every `kat/*-genmc.kat` model, and the graphs of
`tests/oracle/extensible` that refute it, for IMM, LKMM and the two models
there; when `lake` is found too,
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
compare-and-swaps), and the edges `rf`, `mo`, the dependencies, `tc`, `tj` and
`lin`. The reference is the oracle's semantics as it stands: `Graph` has a
concrete mode, in which every unknown is a constant, so every formula over the
graph folds to one, and the code that gives `.kat` its meaning for the solver
gives it on the single graph. (`Term` keeps a constant as a plain truth value
and makes it a solver term only on demand, which made this six times faster.)

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

The graphs are those GenMC builds: they satisfy the oracle's axioms, their
RMWs are atomic (in `co`, an RMW's write comes right after the write its read
reads), and they have no cycle of `po | rf | tc | tj | lin` (for IMM and LKMM,
of GenMC's prefix relation, `(ppo | rfe | tc | tj | lin)+`). For a graph with
`lin`, that is the graph without it: Relinche adds `lin` to a graph GenMC
built, whatever cycles it closes. Dependencies come from reads, and go to the
events GenMC records them for (not thread starts, method calls, or the write
of an RMW).

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

`G` is coherent when the view `export coherence` names, composed with
`(rf | mo | fr)+`, is irreflexive. LKMM's user predicates mean what the GenMC
code `kat/lkmm-genmc.kat` gives them does, on the labels the runner makes;
`prop-int`, which GenMC computes by hand (`prop_int_preds`), is
`(prop \ id) & int`.

The graphs are every one up to a number of events (thread starts aside),
threads and locations, over instructions that tell apart what the model does:
SC's `na` and `sc` accesses; TSO's, RA's and RC11's orderings; RMWs and fences;
for IMM and LKMM, a dependency on the read before an event; for LKMM its twelve
kinds of fence, locks and unlocks, SRCU, and its RMWs. And random graphs of up
to `--random-events` events, with thread creation and joins, method calls and
`lin`, each of a few instruction kinds or of one ordering: half of them built
as GenMC builds a graph (events in a random interleaving, each read reading
from a write, and each write going in `co`, where the graph so far stays
coherent), half anything the axioms allow.

The ctests labeled `genmc`, one per model, are built when `GENMC_SOURCE_DIR`
(a CMake variable, or the environment variable when configuring) names a GenMC
source tree; the build makes its core library without LLVM. Each takes about a
minute:

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
| random graphs | 100000 | 100000 | 100000 | 100000 | 100000 | 200000 |
| `isConsistent(G)` | 1584510 (187085) | 508207 (20460) | 187326 (0) | 1378894 (1740) | 7306486 (11588) | 562162 (1399) |
| `isConsistent(e)` | 3285060 (135372) | 1019919 (15611) | 335214 (0) | 2915110 (1026) | 11788590 (9217) | 828330 (1141) |
| views | 32.0M | 9.1M | 3.9M | 23.4M | 107.2M | 5.8M |
| prefixes | 10.7M | 3.0M | 1.3M | 7.8M | 35.8M | 2.9M, and 2.9M of `rppo` |
| `getCoherentStores` | 1495816 (396942) | 400154 (66358) | 101259 (16636) | 1185687 (200533) | 4789424 (1003086) | 237175 (27018) |
| `getCoherentPlacings` | 1532211 (417274) | 432421 (75846) | 148883 (24355) | 1240301 (212409) | 4864352 (1019148) | 250493 (28992) |
| `filterCoherentRevisits` | 673967 (64997) | 140654 (8565) | 35379 (2125) | 429858 (26026) | | |
| `isCoherentRelinche` | 6819 (422) | 6881 (300) | 6336 (282) | 6687 (329) | 6351 (471) | 13640 (751) |
| disagreements | 0 | 0 | 0 | 0 | 2 | 0 |

(RA's consistency is coherence alone: its `isConsistent` is always true.)
The two disagreements are a bug, filed as
[#27](https://github.com/vzhn/kater-fork/issues/27): two random graphs of IMM
whose method calls `lin` orders in a circle, so that `hb` and then `psc` have a
cycle, which the full `isConsistent(G)` misses. The answer depends on the
order the check explores the labels in: renumbering the threads of the graph
they shrink to makes it find the cycle. The traversal `GenMCPrinter`
prints for acyclicity never explores a (state, label) pair again once it has
finished it, and the full check keeps these marks across its starting labels,
so a pair finished while no starting state was on the stack hides the cycles
through it (see [Open issues](#open-issues)).
`tests/oracle/genmc/graphs/issue-27.graph` is that graph; the ctest
`oracle-genmc-issue-27` replays it and fails once the bug is fixed. Another
20000 random graphs per model, with `lin` free to close cycles in all of
them, found five more for IMM and none for the other models.

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

- `checkErrors` and `checkWarnings`: their `unless` clauses use `alloc`, `free`,
  `retire`, `unprotected` and `last_*`, which the oracle has no meaning for.
- Revisits under IMM and LKMM, whose revisited graph has holes, and the
  reads-from of the reads in it (`GenMCDriver::getRevisitView`), which is
  GenMC's driver more than the checker; and reads added before events a revisit
  kept, which GenMC's LKMM mode relocates.
- Labels the instructions do not make: allocation and freeing, hazard
  pointers, abstract locks, helped compare-and-swaps, barriers, condition
  variables, thread kills; and GenMC's hand-written LKMM checks (RCU, plain
  accesses).

## Extensibility

GenMC explores a program by adding one event at a time to a consistent
graph, and relies on every addition having a consistent outcome: otherwise
an exploration stops at a graph whose completions it was meant to reach.
This is *extensibility* (Definition 5.4.1 of Kokologiannakis's thesis);
TruSt (POPL'22) asks it of the event added *maximally*, reading from the last
write in `mo`, or last in `mo` (*maximal extensibility*). GenMC adds an event
once its predecessors in its prefix relation, `pporf = (ppo | rfe | tc | tj |
lin)+` (`KatModule::createPPORF`), are in the graph. When `ppo` is `po` (SC,
TSO, RA, RC11), that event is the last of its thread and nothing follows it:
added maximally, it has no outgoing edge, and closes no cycle of a model
whose constraints use relations only positively (§3.8 of the Kater paper).
When `ppo` is not `po` (IMM, LKMM), a revisit keeps the revisiting write's
`pporf`-prefix and drops the events `po`-before it that are not in it; GenMC
adds those later, into the hole, and such an event has `po`-successors
already, to which the constraints may relate it (HMC, ASPLOS'20, walks
through one: in load buffering, the read of the second thread is added after
the write that follows it).

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

Neither IMM nor LKMM has this property. The oracle finds an event each cannot
add, on graphs larger than the ones it searches (in `tests/oracle/extensible`,
checked by the ctests `oracle-extensible-refuted-*`):

- `imm-addr-po.graph`, 11 events: a read in a hole between an event it
  depends on by address and a write. Added, whatever it reads, it orders the
  two (`[DEP] ; addr ; po ; [W]` is in `ppo`, by the `addr ; po?` of `deps`)
  and closes an `ar` cycle through an `FSC ; hb ; eco ; hb ; FSC` step;
  without it, the graph is consistent. GenMC can leave this hole: the write's
  prefix, computed with the read there, has the first event and not the
  read, which a revisit by the write then drops.
- `lkmm-moe.graph`, 8 events: a write in a hole before a read of its
  location, which reads a write of another thread. Coherence puts the added
  write `mo`-before that write, its only place, and the `moe` step closes a
  `pb` cycle. GenMC leaves such a hole only once the other write's prefix
  reaches past the added write in its thread (`isCoBeforeSavedPrefix`, in
  `GenMCDriver::isMaximalExtension`).

And IMM is not maximally extensible. In `imm-join.graph`, 13 events, a read
in a hole before a thread join, read from a release write, makes the join
synchronize with that write (`sw_to_f`: `rf ; po ; [TJ] ; [ACQ]`), and closes
an `ar` cycle; `ppo` does not order the read before the join (`bob` has
`po ; [F]`, not `po ; [TJ]`). Read from init, it closes none
(`oracle-extensible-maximal-refuted-imm-join`).

### What Kater checks

`Checker::isPPOIntersectionInPPO`, for each acyclicity export, and
`Checker::isCoherenceExtensible`, for the coherence export, are the
exporter's checks of extensibility ("Check extensibility" in
`Exporter::checkExportRequirements`). Together they prove maximal
extensibility, for the events that nothing after them in their thread
accesses the location of:

> For every consistent graph G0, and every event e GenMC may add to it (in G0
> with e, nothing follows e in `pporf` and nothing reads from it, and e is
> neither part of an RMW nor a thread start or create) such that no event
> `po`-after e in G0 accesses e's location: G0 with e added maximally (a read
> reading from the last write in `mo`, from init if there is none, a write
> last in `mo`) is consistent.

When `ppo` is `po`, this is the property above: nothing is `po`-after e.
When it is not, it leaves out the events in a hole with a later access to
their location, out of which coherence forces an `eco` step
(`lkmm-moe.graph`): on the graphs up to 3 events, 4760 of the 10915 events
IMM adds into a hole, and 45348 of LKMM's 198645.

Each check takes the automaton of its constraint, for coherence the view
composed with `(rf | mo | fr)+`, a word of which from an event back to it is
a violation; without `lin` steps, which GenMC adds to complete graphs only,
for Relinche. For every state the automaton can enter by a relation step, and
every relation step it can leave the state by first (in the next word, where
a word can end there), it asks about the step unless

- it is an `eco` step: e added maximally has none out of it (no write is
  `mo`-after it, nothing reads from it, and, reading from the last write, no
  `fr` step leaves it);
- the cycle can do without e there, after every step into the state: the
  steps into e and out of it are both within `po`, and the automaton reads a
  step that includes `po` (`po-loc`, if both are within it) from where the
  first starts to where the second ends;
- the event there cannot be one GenMC adds alone: the check adds
  `[NEXCL & ~TB & ~TC]` to what the cycle checks of it, and leaves out the
  steps whose checks do not compose with it (GenMC adds a thread's start
  along with its create, `GenMCDriver::handleThreadCreate`, so a create
  always has `tc` after it).

It decides that each step it asks about, followed by the rest of its word,
is in `pporf ; any*`. For coherence, a step that leaves e where the word
begins is followed by the whole word, which ends at e again, and it may also
be in `po+ ; (rf | mo | fr)+`. Why this proves the property:

- A cycle of the graph with e that does not pass e is a cycle of G0: every
  builtin relation relates two other events with e as it does without it, or
  less (the positional ones, like `po-imm`, only gain pairs when e goes). A
  relation GenMC computes need not: LKMM's `prop-int` can relate two events
  by a path through e. The check takes it for one that does.
- So a new cycle visits e, and leaves e at each visit by a step that is not
  `eco`. If at every visit the steps into e and out of it are within `po`,
  and the constraint's automaton reads a `po` step past them, the cycle with
  one `po` step instead of each such two is a cycle of G0. At a visit where
  this is not so, the rest of the word from e is in `pporf ; any*`, and e
  has a `pporf` successor.
- e added maximally has no more `pporf` successors than it has in G, none:
  the steps out of it are those it has in G, but the `eco` ones (and
  `detour`, which needs a `moe` step out of it).
- A violation of coherence is a single word of the view and `eco`; a visit
  at the event it starts from reads it back to that event, e, and if it is
  a `po` path and then `eco`, the event the path reaches is a later access
  to e's location.

The check needed four facts the theory lacked: thread creates and finishes
release, thread starts and joins acquire (`TC <= REL`, `TE <= REL`,
`TB <= ACQ`, `TJ <= ACQ`, and all four `ATOM`), the orderings GenMC gives
their labels. The audit finds them true; no exported checker changes.

SC, TSO, RA and RC11 pass. The two models of `tests/oracle/extensible` fail,
at the step out of the write added into the hole (`[W] ; po ; [W]`, and the
`po` step before the acquire read), and their exports fail with them
(`oracle-export-issue-33-*`). IMM fails at the visits of the two graphs
above: a step out of a read entered by `addr`, and the `po` step from a read
entered by `rf` to a join. LKMM fails where e leaves by `prop-int`, which
Kater cannot see into, and where the `pporf` step out of e needs an
inclusion between LKMM's own predicates, which Kater does not know
(`UL <= Rel`, ...).

A model can say that an export is not extensible: `export nonextensible
acyclic r` (or `coherence`). The check of that export then only warns, and
warns as well, that the flag is stale, if it passes. IMM flags `ar`, `psc`
and its coherence export ([#38](https://github.com/vzhn/kater-fork/issues/38)),
LKMM `lkhb` and `pb` ([#39](https://github.com/vzhn/kater-fork/issues/39)),
and their checkers are unchanged; the ctests `export-nonextensible-*` fail
once either exports without the warning.

### What the oracle checks

- `kater-oracle export` records each extensibility check by its
  certificates: both checks hand theirs to the certificate sink, with the
  constraint, as `checkInclusion` does with the subset constraint it decides
  (the coherence check two, for the steps that leave e within its word and
  where the word begins). The export check checks each certificate, the
  letter inclusions it rests on, and the inclusion between its two automata
  on every graph up to N events, and reports it as `vacuous` when its left
  automaton accepts nothing, as all seven acyclicity checks of
  `kat/*-genmc.kat` did before #33 was fixed; none does now. Every claim of
  the six exports holds up to 3 events; at 3, each claim of LKMM's coherence
  check takes minutes, so the ctests check LKMM up to 2 events
  (`oracle-export-lkmm`) and the others up to 3 (`oracle-export`). With
  `--json`, it writes these certificates with the others; the checker in
  Lean accepts the 67 certificates of the six exports (13 of them the
  extensibility checks'), and gives each of their 841 copies
  `checkCertificate`'s verdict.
- `kater-oracle extensible` checks both properties on concrete graphs:
  every graph `kater-oracle genmc` enumerates (3 threads, 2 locations, thread
  events aside), each event in it GenMC may add, and every way of adding the
  event to the graph without it, and, for the events with no later access to
  their location, the maximal way (each graph without the event is taken
  once, from the first of the graphs that add it, so that the cost stays
  that of the enumeration). With `--maximal`, the maximal additions decide
  its verdict too.

| | SC | TSO | RA | RC11 | IMM | LKMM |
|---|---|---|---|---|---|---|
| every graph up to 3 events | 2480 | 10533 | 3294 | 24769 | 66901 | 367790 |
| events added to a consistent graph | 3615 | 16128 | 4914 | 37992 | 97447 | 684992 |
| of which into a hole | 0 | 0 | 0 | 0 | 10915 | 198645 |
| that cannot be added consistently | 0 | 0 | 0 | 0 | 0 | 0 |
| with no later access to their location | 3615 | 16128 | 4914 | 37992 | 92687 | 639644 |
| that cannot be added maximally | 0 | 0 | 0 | 0 | 0 | 0 |

The six models are extensible on these graphs, and maximally so for the
events Kater's check is about; at 3 events, LKMM takes 13 minutes, IMM 40
seconds. Their counterexamples need 8 events and more (above). The ctests
`oracle-extensible` (up to 3 events) and `oracle-extensible-lkmm` (up to 2)
check the six models with `--maximal`; `oracle-extensible-refuted-*` the two
of `tests/oracle/extensible`, IMM and LKMM at their graphs, and
`oracle-extensible-maximal-refuted-imm-join` the one where IMM can add the
event, but not maximally.

## Findings

All fixed, with a regression test each. Most were found by the oracle, the
others by running Kater under sanitizers, by type-checking exported checkers,
and by reading the code. The files in `tests/wrong/soundness` are false claims
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

16. **The extensibility check decided nothing** ("Checker: an extensibility
    check that decides something"; #33). `isPPOIntersectionInPPO` looked for
    the `eco` steps among the incoming transitions of states, whose labels
    are inverted (`rf^-1`), found none, and so cut nothing: its left
    automaton accepted no word, and the check held of every model, as it had
    since v0.3. Turned around, it would not have established extensibility
    either: its starting states left out every state an `eco` step can
    follow, and a `pporf` step somewhere in each stretch between `eco` steps
    does not keep the added event out of a cycle. It now decides what
    [Extensibility](#extensibility) describes; Kater rejects the two models
    of `tests/oracle/extensible` it used to export
    (`oracle-export-issue-33-*`), and finds IMM and LKMM not extensible
    (#38, #39), which the oracle confirms. Found by handing the check's
    certificate to the export check, which found its left automaton empty.

Items 1–4, 7, 8, 11 and 13 made Kater prove false claims, 12 and 14 could
have, 15 made it run forever, and 16 let it export models GenMC cannot
explore; the others crashed it, read memory it should not, or produced code
GenMC rejects.
Under the sanitizers the whole suite, the unit tests, 4000 fuzzed files and the
export of every `kat/*-genmc.kat` model now run without a report, and the
exported checkers are the same as without them.

After the fixes:

- the audit finds no false fact: 3016 hold, up to 4 events, with the
  inclusions between whole letters and the four facts on thread events of
  #33's fix (2108 before both, 2960 before the latter);
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
  rewrites with up to 5 events, and 488 letter inclusions of the claims'
  certificates, before #33 was fixed (7 of the claims the extensibility
  checks, which were vacuous); since, 923 claims, rewrites and letter
  inclusions up to 3 events, with 13 extensibility checks, none vacuous;
- every model is extensible on every graph up to 3 events, and maximally
  so for the events Kater's extensibility check is about (see
  [Extensibility](#extensibility));
- the exported checkers of all six models type-check against GenMC
  (0.19.0-vzhn.10) and are byte-identical to the ones before the fixes;
- run inside GenMC, they answer as the reference semantics does, but for
  graphs that hit [#27](https://github.com/vzhn/kater-fork/issues/27), still
  open (see [Results](#results)).

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
- **The exported acyclicity checks can miss a cycle**
  ([#27](https://github.com/vzhn/kater-fork/issues/27)): the DFS
  `GenMCPrinter::outputTraversal` prints for them never explores a
  (state, label) pair again once it has finished it, and the full check keeps
  these marks across the labels it starts from, so a pair finished while no
  starting state was on the stack hides the cycles through it. Found by
  `kater-oracle genmc` on IMM, on graphs whose method calls `lin` orders in a
  circle; `tests/oracle/genmc/graphs/issue-27.graph` is the reproducer, and
  the ctest `oracle-genmc-issue-27` fails once this is fixed. Tarjan's
  algorithm over the pairs, or a nested DFS, would decide the cycles exactly.
- **IMM and LKMM are not extensible**
  ([#38](https://github.com/vzhn/kater-fork/issues/38),
  [#39](https://github.com/vzhn/kater-fork/issues/39)): GenMC can leave a
  hole in an IMM graph that no way of filling keeps consistent (`addr ; po?`
  orders events through it), and in an LKMM graph (coherence ties the event
  to a later read of its location by `moe`), on graphs of 11 and 8 events in
  `tests/oracle/extensible`. Both flag their exports `nonextensible`, and
  export with a warning. A fix changes their `ppo`, or which holes GenMC
  leaves (`GenMCDriver::isMaximalExtension`).
- **What the extensibility check leaves out.** It proves extensibility for
  the events that nothing after them accesses the location of; in a hole,
  an event with a later access to its location has an `eco` step out of it
  that coherence forces, which the check does not follow (4760 of IMM's
  10915 events into a hole on the graphs up to 3 events). It takes a
  relation GenMC computes for one that relates two events the same way with
  or without the event GenMC adds, which LKMM's `prop-int` need not.
- **Not checked by the oracle**: of the printed code, the error and warning
  checks and the revisits of the dependency-tracking models (see
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
