# A checker of Kater's certificates, proved sound

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

`lake build` checks the proof and builds `kater-cert-check`. To check the
certificates of Kater's test suite, from the repository's root, with a build
configured with `-DBUILD_TESTS=ON`:

    Release/kater-oracle certify -n 1 --json /tmp/certificates tests/correct/*/*.kat
    cd formal && lake exe kater-cert-check /tmp/certificates

`ctest -L formal` does the same.

The Lean mirrors parts of Kater's C++: its letters, its certificates,
`checkCertificate`, the evidence of the saturations, the chain and their
checks, the oracle's meaning of letters and automata, and the JSON writer. Those parts are marked in the C++ with `formal: begin` and
`formal: end` comments, and `mirrors.txt` records a hash of each as of the
last review of the Lean against it. `scripts/check-mirrors.sh` reports the
regions that changed since, with the Lean to review, and every build of
Kater warns about them; after the review, `scripts/check-mirrors.sh
--update` records them as they are.

See `doc/verification.md` (The checker in Lean, Evidence of the
saturations) for the model, what the proofs need, and what remains trusted.
