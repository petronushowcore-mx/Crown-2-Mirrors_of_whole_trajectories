# mirrors: executable companion

Run the commands below from this directory with Python 3.10 or newer. Checks remain active with Python optimisation enabled. Only the Python standard library is required; the Python checks make no network or model-provider calls.

```sh
python harness.py --teeth
python harness.py --teeth --json outcomes.json
python break_harness.py
python -O harness.py --teeth --json outcomes-optimised.json
python -O break_harness.py
```

The first two commands execute the same 8 named checks. Success exits 0; a failed assertion or execution error exits nonzero. The optional JSON records every named outcome. The third command first checks the unchanged model, then transforms isolated temporary copies in 21 cases. Each named check has one scientific mutation of the model, which must fail first at that check. Eight further damaging transformations must each fail first at the check named in the table below, and five equivalent transformations must leave every check passing; each equivalent transformation has a damaging one at the same site. It writes mutation-report.json with source hashes, exact outcomes and captured output; an incomplete run is not a passing result. The last two commands run the same checks and mutations with optimisation enabled, writing outcomes-optimised.json and mutation-report-optimised.json. The mutation runner passes its own optimisation setting to every child process. Each invocation replaces its own generated output files; archive them first if retaining multiple runs.

| Site | Equivalent, must pass | Damaging, first failure |
|---|---|---|
| total of charged costs | local parameter renamed | constant total: M05 |
| lifted step | | destination-image condition dropped: M02 |
| lift root | | root-image condition dropped: M02 |
| target states of the M02 example | swapped in the image and in every target path | swapped in the image only: M02 |
| periodic tail | the same tail with a doubled period | prefix sliced in place of the tail: M04 |
| recurrence verdict | decided on a doubled period | decided by the first symbol of the period: M04 |
| charge of one event | | signed charges that can cancel: M07 |
| charge of a word | the same absolute charges added in reverse order | only the final amplitude charged: M07 |

## Scope

The labels M01–M08 name the checks of this companion; results of the manuscript are cited as propositions.

M01: exact decoding on all binary observations and verdicts on three histories.
M02: rooted path lifting versus global path coverage. A lift starts at the declared root, whose image must be the first target state, and each step must reach a vertex with the next target image; an existing edge whose destination has the wrong image does not lift.
M03: one common witness versus separate witnesses.
M04: equal finite prefixes with different infinite recurrence verdicts, on ultimately periodic words. Observations continue past the shared prefix with explicit tail values, and a recurrent periodic tail may begin with zero.
M05: charged residual budget versus a reset counter.
M06: requested restart versus intrinsic restart capability, as the two-input slice of the Proposition M10 law at the completion phase, without the blocking input. The complete three-signal law is executed in deep/suite.py by t_M05_full_restart_automaton and t_M09_capability_channels.
M07: geometric upkeep, exact rational arithmetic and a positive witness floor, with the maintenance law of Proposition M15: each event costs c|σ| from one budget R. On every word of up to three events over the amplitudes −2, −1, −1/3, 0, 1/3, 1 and 3/2, with three declared pairs of c and R, running charges and paid prefixes are compared with balances debited independently. With declared rational floors s, at most R/(cs) events are paid and a held floor of either sign is refused at the first event past ⌊R/(cs)⌋; exact caps and first unaffordable events are included. The geometric witnesses are paid at every executed horizon up to 100 events, and the remaining balance equals the witness.
M08: two binary shares, individually uninformative and jointly sufficient.

## Extended relational models

The deeper companion is in [deep/README.md](deep/README.md). It adds exact finite families, independent complete-assignment enumeration, executable relation maps, ambiguity witnesses, and model mutations. From this directory, run this work and its shared relation checks:

```sh
python deep/suite.py --work mirrors --profile full --json deep-mirrors-result.json
```

The deep README also gives the complete population and mutation commands. Its source index pins manuscript anchors and states which scientific claims remain outside finite execution. The smaller examples above remain available with the scope stated above.

## Limits

The Python examples are finite or exactly ultimately periodic models. They do not prove arbitrary infinite-history, smooth-cohomology, inverse-limit or dynamical claims, and do not identify Operator Zero. Payment is executed on finite words and finite horizons; the infinite-horizon statements of Proposition M15 retain their text proofs. M06 does not model the blocking input. Existing Lean material is included under lean/ with its recorded toolchain and byte-bound earlier compilation results. Manuscript-to-formal-model correspondence remains a mathematical obligation, not a consequence of compilation.

The source manifest pins the packaged manuscript and program bytes. It records provenance, not a verdict of scientific completeness. The code and its usage instructions use the MIT licence in LICENSE-code.txt; the manuscripts retain their own stated licence, which is not replaced by the code licence.
