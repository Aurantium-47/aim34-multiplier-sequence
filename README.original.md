# AIM 2007 Problem 34: independently accepted full formal proof (v2)

Independent verdict: FULL PASS for the full actual-preserver target, for every positive real shift.

For every real m>0, the sequence a(n)=(n+m)^(sqrt(n+m)), n>=0, is not a multiplier sequence: the actual real polynomial coefficient operator

    sum c_n X^n  ↦  sum a(n)c_n X^n

fails to preserve real-rootedness. The proof explicitly includes a finite real polynomial counterexample existence theorem for each shift. It does not give a uniform counterexample degree. Positive integer shifts and the original one-indexed convention are both covered.

The source is the AIM workshop “Pólya–Schur–Lax problems: hyperbolicity and stability preservers”, A List of Open Problems, compiled by Julius Borcea, Petter Brändén, George Csordas and Victor Vinnikov, Problem 34 (2007), also restated as Problem 58 in Matthew Chasse's 2011 dissertation. Exact source links and PDF hashes appear in PINS.json and PROOF_OUTLINE.md.

Final declarations, all in namespace AIM34:
- not_multiplier_shiftedRadicalPower
- exists_counterexample_polynomial
- fullProblem34
- problem34_positive_integer_shift
- problem34_one_indexed_shift

The source freeze contains 22 modules, including the author axiom/type audit. The proof uses actual polynomial Jensen operators and a zero-safe forward-difference argument, followed by a fully proved Newton interpolation and half-plane Schwarz uniqueness contradiction. No multiplier-sequence classification, Carlson theorem, interpolation premise, or auxiliary sign hypothesis is assumed in the final theorem.

All 57 retained author logs are included, including 26 failed elaboration logs. Historical failures and snapshots are evidence, not accepted mathematical imports. Source files at package root alone form the author import closure; compile them in build_order.txt order.

No novelty, priority, publication, or source author's original contribution is claimed. PROOF_OUTLINE.md identifies reused generic root-product lemmas. The earlier ordinary proof and source audits are preserved as historical provenance; their old status text does not certify this new formalization.

## Reproduction

Supply an already provisioned Lean 4.19.0 environment and dependencies built from mathlib commit c44e0c8ee63ca166450922a373c7409c5d26b00b. Set AIM34_PINNED_ENV to the environment file exposing only the matching compiler and external dependency paths, and AIM34_MATHLIB_ROOT to that pinned source repository. Run ./verify_frozen.sh. It checks the source commit and compiler version, isolates custom sources, compiles serially and runs independent semantic guards. It never downloads or installs anything; memory is capped at 4 GiB and Lean stack at 16 MiB. SOURCE_SHA256SUMS.txt and source_manifest.json identify the exact mathematical source bytes.

Independent review freshly replayed all 22 source modules and two audit modules. It checked all 164 explicit author declarations plus six independent expanded guards, 229 complete safe records, and the 43,667-constant logical closure. Only propext, Classical.choice and Quot.sound occur as axioms. See independent_review/INDEPENDENT_REVIEW.md for exact evidence and limits.
