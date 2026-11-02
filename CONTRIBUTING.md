# Contributing

Contributions to stereochemical specifications, Lean proofs, executable algorithms, examples,
and build tooling are welcome. Read [README.md](README.md) and [BUILDING.md](BUILDING.md) first.

For a proof change, state the exact theorem and assumptions. Preserve the distinction between
an evaluator's operational behavior and its independent chemical meaning. Do not introduce
`sorry`, `admit`, or axioms in place of proofs. Keep existing import paths compatible.

For a chemistry issue, provide a molecular representation, geometry or stereochemical
configuration, expected assignment, and the relevant sequence-rule reasoning. A counterexample
is useful even when a repair is not yet known.

Run focused checks for the changed modules under aggregate memory limits, and report which
checks actually ran. Use `python3 -B tools/check_source_tree.py` for a static source check.
The source check and CI do not certify chemical completeness or compile the proof library.

Keep changes focused, describe remaining limitations, and credit mathematical, chemical, and
software contributions. Follow the [Code of Conduct](CODE_OF_CONDUCT.md). Report sensitive
issues through the process in [SECURITY.md](SECURITY.md).
