# Lean sources

These six unchanged source files match the SHA-256 values in compilation-record.json, which preserves their earlier compiler results. Packaging did not rerun compilation. The declared toolchain is in lean-toolchain; Mathlib is pinned in lakefile.toml. Files reuse names and are checked separately, not imported together; declaration counts across files must not be added as a count of distinct theorems.

With elan and network access for initial dependencies, run from this directory:

```sh
lake update
lake exe cache get
lake env lean MirrorCausalLifting.lean
lake env lean MirrorChargedResidualR2.lean
lake env lean MirrorNativeClassInverseLimit-r3p.lean
lake env lean MirrorNumericalInterfaces-p.lean
lake env lean Mirrors.lean
lake env lean MirrorsComposition.lean
```

The manuscript scope clause L10 lists what is formalised and the exclusions. These commands check formal statements; they do not establish the correspondence between every informal sentence and those statements. No V3 source is included or tested. Reproduction commands above were not rerun during this packaging step.
