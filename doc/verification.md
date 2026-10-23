# Verifying Kater

Kater proves assertions about memory models and exports consistency checkers
for GenMC. A wrong "holds" is the worst failure it can have: a metatheoretic
result that is not true, or a checker that accepts executions the model
forbids. This document describes how Kater is checked against an independent
semantics, the contracts its decision procedure has to meet, and what the
checking has found so far.

Everything here is *bounded* testing: a claim is refuted by a graph of at most
N events, or not refuted up to N. It finds bugs; it does not prove their
absence. The contracts below are the lemmas a proof has to establish (see
[Next steps](#next-steps)).

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
  cycles. `total r` has none either (see [Open issues](#open-issues)).
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

Every fact the Theory states about the builtins: inclusions between relations
(`Theory::isIncludedIn`), domains and codomains, inclusions and disjointness
between predicates, the label pairs that do not compose, the relations treated
as eco, the per-location variants, and the built-in assumptions
(`fr;mo <= fr`, `po;po <= po`, `mo;mo <= mo`, `rf;fr <= mo`).

    kater-oracle transforms [-n EVENTS] [--cases N] [--seed S] [--depth D] [--only PASS]

Each automaton pass against its contract (below), on the automata of random
expressions.

    kater-oracle export [-n EVENTS] FILE...

Exports FILE into a scratch directory and checks what the export relies on:
every claim the Checker proves on the way (recorded with
`Checker::setObserver`), and that every definition the exporter rewrites keeps
its meaning.

    kater-oracle certify [-n EVENTS] FILE...

Has Kater prove FILE's assertions with certificates
(`Checker::setCertificateSink`), checks each certificate without searching
(below), and checks every letter inclusion the certificates rest on against
the semantics.

    kater-oracle explain FILE...

The left-hand automaton of each assertion through the stages of the inclusion
check, for triage.

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
certificates, the soundness regressions with `--refutable`, and the export
check of every `kat/*-genmc.kat` model:

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
| `saturateEmpty`, `saturateID`, `saturateTransitive`, `saturateBuiltin`, `saturateTotal`, `saturateSubword` (right-hand side) | under H, `[[T(N)]] ⊆ [[N]]` |
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

Items 1–4, 7, 8 and 11 made Kater prove false claims, and 12 could have; the
others crashed it, read memory it should not, or produced code GenMC rejects.
Under the sanitizers the whole suite, the unit tests, 4000 fuzzed files and the
export of every `kat/*-genmc.kat` model now run without a report, and the
exported checkers are the same as without them.

After the fixes:

- the audit finds no false fact (2108 hold, up to 4 events);
- the transformation contracts hold on random expressions: over 1000 at
  depth 3 and 800 at depth 4 for every pass, up to 4 events, and 1600 more at
  depth 4 for the predicate passes;
- the fuzzer finds no unsound proof in 25500 files, of which Kater proved
  8521, across all profiles;
- every assertion of `tests/correct` has no counterexample with up to 5
  events, and every proof of it has a valid certificate (54, resting on 498
  letter inclusions that hold);
- the export of every `kat/*-genmc.kat` model passes: 215 claims and
  rewrites with up to 5 events, and 488 letter inclusions of the claims'
  certificates;
- the exported checkers of all six models type-check against GenMC
  (0.19.0-vzhn.10) and are byte-identical to the ones before the fixes.

## Open issues

- **`assume total r`** has no documented meaning. Kater saturates it as if
  `r` were reflexive and transitive: it proves `id <= r` and `r;r <= r` from
  it. That is unsound if `total` means a strict total order, as `mo` is. The
  oracle reports the constraint as unsupported.
- **Incompleteness.** `tests/wrong/equivalence/eq-ra1-ra2-no-universe.kat`
  has no counterexample with up to 5 events: it is probably true, but outside
  what Kater can prove. The four files of `tests/wrong/compilation` have none
  with up to 5 events either; two of them state assumptions Kater ignores
  (`po?;[R] <= [F];po;[R]` even rules out reads), the others need larger
  graphs.
- **`addTransitivePredicateEdges` depends on the order of states.** It
  merges two consecutive predicates into a shortcut, adding the shortcut as
  soon as it visits the first state and removing the second step at the end.
  Through three consecutive predicates (`0 -[]-> 2 -[ACQ&F]-> 16 -[]-> 18`) a
  shortcut can be added to a state and later removed with that state's steps,
  so the path is lost; the contract test found this on automata straight from
  `toNFA`. In the context `normalize` calls it in (after `simplify`,
  `saturateDomains` and `breakToParts`), no violation showed in 1600
  expressions of depth 4, and `normalize` itself none in 800 more, so it
  does not seem reachable; the contract tests now run the pass in that
  context. Computing the closure of predicate paths first, then replacing,
  would remove the dependence.
- **Inverses of recursive relations.** `x^-1` for a `let rec x` flips the
  definitions in place, and Kater's automaton construction does not recognize
  the flipped self-reference `x^-1` as the recursion: it treats it as an
  unknown relation. That is sound (what holds for every relation in its place
  holds for `x^-1`) but incomplete: Kater cannot prove that the inverse of
  `let rec x = po | x;rf` is within `(po^-1 | rf^-1)+`.
- **Performance.** Four of 10000 random files took Kater over 30 seconds. All
  four assume a relation equal to a predicate or within `id`
  (`assume data = [EXCL]`, `assume po-loc = [DEP]`, ...): `saturateID` adds a
  copy of the assumption's automaton at every state of the right-hand side,
  and the result grows past what the inclusion check handles.
- **Not checked by the oracle**: `isPPOIntersectionInPPO`, which the exporter
  uses to prune acyclicity checks (it is not a constraint the observer sees);
  and the printed code of `GenMCPrinter`, beyond type-checking it.
- The oracle trusts Z3, its own axioms, and Kater's parser, which it shares.

## Next steps

1. **Certificates.** Kater emits certificates of its final step, and
   `kater-oracle certify` checks them (see [Certificates](#certificates)).
   What remains is a checker whose correctness is itself proved, and
   certificates for the steps before: the passes, which could either be
   proved once from their contracts or emit evidence of their own (the
   saturations, for instance, which paths they added for which hypothesis).
2. **Formalization.** The model above is the specification: graphs and their
   axioms, the meaning of the builtins, of expressions and of automata. The
   contracts of the passes and the audit's facts are the lemmas. The oracle's
   counterexamples fix the corner cases a formalization must get right (the
   initial writes, `po-loc-imm`, same-location for non-accesses).
3. **The printer.** Differential testing of the exported checkers inside
   GenMC: graphs from the oracle, run through the generated `isConsistent`,
   against the model's acyclicity constraints evaluated by the oracle.
