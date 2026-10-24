# Checkers of Kater's proofs, proved sound

When Kater proves an inclusion between two automata, it can hand out a
certificate of the proof (`Checker::Certificate`). This Lean 4 project has a
checker of these certificates and a proof that it is sound: if it accepts a
certificate, and the letter inclusions the certificate rests on hold, the
left automaton's relation is within the right one's.

The certificate also records how its right automaton came from the
right-hand side (`Checker::Chain`): each saturation with the hypothesis it
used, and evidence that under the hypothesis it added nothing the automaton
before it did not denote (`SaturationEvidence`). The project checks the
evidence too, and proves that if both checkers accept, and the hypotheses
and letter inclusions hold, the left automaton is within the automaton of
the right-hand side, but for the passes without evidence (`normalize`,
pruning), whose contracts stay hypotheses.

Kater can also hand out the evidence of a whole proof (`Checker::Evidence`):
the automata of every stage of an inclusion check, from the assertion's
expressions to the certificate. The checker of whole proofs checks every
step of it, against its own automata of the expressions and its own theory
of Kater's builtins, and the project proves the end-to-end theorem: if the
checker accepts the evidence of an assertion, the assertion holds on every
execution graph, in a model of them, where the module's declarations and
assumptions hold.

The claims an export rests on have evidence too: the inclusions the Checker
proves on the way, as for assertions, and each extensibility check of an
acyclicity or coherence constraint (`Checker::ExtensibilityEvidence`). The
checker checks the inclusions of its words, builds the words again from
the constraint's automaton, which it checks against the constraint, and
requires them within Kater's; the project proves that the constraint of an
accepted check is extensible: on every graph of the model, adding an event
GenMC may add maximally keeps it if the graph without the event had it.

| File | What it has |
|------|-------------|
| `KaterCert/Rel.lean` | relations on events |
| `KaterCert/Label.lean` | Kater's letters and what they mean |
| `KaterCert/NFA.lean` | automata, and the relations of words and automata |
| `KaterCert/Conditions.lean` | the four conditions of a certificate, and why they suffice |
| `KaterCert/Checker.lean` | `Certificate.check`: `checkCertificate` of `tests/oracle/Certificate.cpp`, in Lean |
| `KaterCert/Soundness.lean` | `check_sound`: the checker is sound |
| `KaterCert/Path.lean` | paths of automata, and what the words reaching a state relate |
| `KaterCert/Saturation.lean` | the evidence of a saturation, and `Evidence.check`: `checkSaturation` of `tests/oracle/Chain.cpp` |
| `KaterCert/SaturationSound.lean` | `Evidence.check_sound`: the check of the evidence is sound |
| `KaterCert/Chain.lean` | the chain of passes, `Chain.check` (`checkChain`), and `Chain.sound`, which joins it to the final certificate |
| `KaterCert/Read.lean`, `Main.lean` | `kater-cert-check`: reads and checks certificates and their chains written as JSON |
| `KaterCert/Exp.lean` | expressions and constraints, and what they mean (`let rec` as a least solution) |
| `KaterCert/Rec.lean` | the normal form of `let rec` definitions, and their least solution as reachability |
| `KaterCert/Thompson.lean` | Lean's own automaton of an expression, and `nfa_denote`: it denotes what the expression does |
| `KaterCert/Theory.lean` | what the checkers ask of a theory, and what makes its answers true |
| `KaterCert/Guarded.lean` | `Guarded.prove`: one automaton within another, as relations, through the theory; a search and a verified check |
| `KaterCert/Loc.lean` | the check of `saturateLoc` |
| `KaterCert/Rotate.lean` | the rotations of an automaton, and the check that `saturateRotate` adds no cycle |
| `KaterCert/Builtin.lean` | Kater's builtins, and the theory Lean builds of them and a module's declarations |
| `KaterCert/Model.lean` | the model: execution graphs, their axioms, and what the builtins mean in them |
| `KaterCert/ModelSound.lean` | the theory is sound, and Kater's builtin assumptions hold, on every graph |
| `KaterCert/Hypotheses.lean` | which assumption gives a saturation its hypothesis, and that the hypothesis then holds |
| `KaterCert/ReadChain.lean` | reads the evidence of whole proofs, and of extensibility checks, written as JSON |
| `KaterCert/Whole.lean` | `checkAssertion`: every step of a proof, and `checkAssertion_sound` |
| `KaterCert/Extensible.lean` | an extensibility check: the inclusions of its words (`checkInclusions`), and Lean's own words, from the constraint's automaton (`checkCycles`) |
| `KaterCert/Cycles.lean` | runs of an automaton over events, and `check_sound`: a cycle through an event GenMC adds does without it, if the words relate it to nothing |
| `KaterCert/Erase.lean` | a graph without one of its events, and the letters that mean the same there |
| `KaterCert/EndToEnd.lean` | `EndToEnd.sound`: the assertion of an accepted proof holds on every graph; `EndToEnd.extensible`: the constraint of an accepted extensibility check is extensible |
| `ChainMain.lean` | `kater-chain-check`: reads and checks the evidence of whole proofs and of extensibility checks |

`lake build` checks the proofs and builds `kater-cert-check` and
`kater-chain-check`. To check the certificates and the whole proofs of
Kater's test suite, from the repository's root, with a build configured with
`-DBUILD_TESTS=ON`:

    Release/kater-oracle certify -n 1 --json /tmp/certificates tests/correct/*/*.kat
    cd formal && lake exe kater-cert-check /tmp/certificates

    Release/kater-oracle evidence --json /tmp/evidence tests/correct/*/*.kat
    cd formal && lake exe kater-chain-check /tmp/evidence

and the evidence of the claims the exports of the GenMC models rest on:

    Release/kater-oracle evidence --export --json /tmp/export-evidence kat/*-genmc.kat
    cd formal && lake exe kater-chain-check /tmp/export-evidence

`ctest -L formal` does the same.

The Lean mirrors parts of Kater's C++: its letters, its certificates,
`checkCertificate`, the evidence of the saturations, the chain and their
checks, the evidence of whole proofs and the passes it comes from, the
extensibility check (its evidence, `exitsToCheck`, `decideExtensibility`),
the builtins and the theory's inclusions, the assumptions the theory takes
in, the oracle's meaning of letters, expressions and automata, and the JSON
writers. Those parts are marked in the C++ with `formal: begin` and
`formal: end` comments, and `mirrors.txt` records a hash of each as of the
last review of the Lean against it. `scripts/check-mirrors.sh` reports the
regions that changed since, with the Lean to review, and every build of
Kater warns about them; after the review, `scripts/check-mirrors.sh
--update` records them as they are.

See `doc/verification.md` (The checker in Lean, Evidence of the
saturations, Whole proofs, and What Lean checks of Extensibility) for the
models, what the proofs need, and what remains trusted.
