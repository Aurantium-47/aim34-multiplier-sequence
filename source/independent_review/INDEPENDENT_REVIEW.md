# Independent review: full AIM 2007 Problem 34

Date: 23 October 2026. Verdict: **FULL PASS**.

This is an independent source, semantic, fresh-kernel-replay and logical-dependency review. It is not human peer review, publication acceptance, or a claim of global priority.

## Exact result

For every real number m > 0, the sequence a(n) = (n+m)^(sqrt(n+m)), indexed from n = 0, is not a classical multiplier sequence. The multiplier operator is literally the coefficientwise map on every real polynomial, and real-rootedness permits the zero polynomial. The result is not limited to finite Jensen tests, selected shifts, or a theorem conditional on forward-difference positivity or an analytic interpolant.

The final declarations are:
- AIM34.not_multiplier_shiftedRadicalPower
- AIM34.exists_counterexample_polynomial
- AIM34.fullProblem34
- AIM34.problem34_positive_integer_shift
- AIM34.problem34_one_indexed_shift

The existential witness theorem provides a finite real polynomial for each positive real shift. It does not supply an explicit polynomial or a uniform degree bound.

## Original-source alignment

The original AIM problem-list page 9 was visually inspected, and its cached source text and the accepted ordinary proof were read. The radical is in the exponent. AIM displays the sequence starting at k = 1 while its exponential generating series starts at k = 0. Chasse's Problem 58 uses the zero-indexed convention. The two formal corollaries cover these conventions by the correct shift replacement.

- AIM source: https://aimath.org/WWN/polyaschurlax/polyaschurlax.pdf
  SHA256: 526a5a9ed0e4cb417034d32b9b5bb57610659b21123f6f4dce3dedde9731df36
- Chasse source: https://math.hawaii.edu/home/talks/thesis.pdf
  SHA256: bfb96ee15c6e1f9ef864b55f322dabb3277fbb8169eb6155cf7d73cc53945ff3
- Accepted ordinary proof SHA256: 59d52912eae6ca7f5152b741ae2aa56b00b36f0ed72af5d2aa470927253f3e35
- Frozen formalization MANIFEST.json SHA256: 861ddf010df9615f347c1fb5ef784b5054291b9ddbe4bb0c2b894204d4c7b87b

AIM34Definitions.lean defines actual all-degree preservation, not a canonical-product criterion. The coefficient identity is proved. FullAIM34.lean has only the positive-shift hypothesis in the final theorem. Six independently written, fully expanded statement guards check the positive-real target, the finite witness, both integer conventions, the FullProblem34 alias, and the literal coefficient multiplier. These guards avoid relying on a suggestive theorem name or an opaque surrogate predicate.

## Mathematical chain checked

1. The actual preserver applied to (1+X)^N yields all finite Jensen polynomials. Only this necessary implication is used; Jensen sufficiency is neither assumed nor required.
2. The padded-degree polar operator proves forward-difference closure of Jensen real-rootedness. The proof retains degree <= M and handles identically zero outputs, constants and degree drops.
3. Shifted quadratic Jensen polynomials give adjacent log-concavity. A separate zero-tail argument proves interval support. The proof does not infer gap-free support from adjacent log-concavity alone.
4. A strict drop in a nonnegative, log-concave, gap-free difference sequence forces boundedness. Repeated summation makes the original sequence polynomially bounded, contrary to the proved faster-than-every-polynomial growth of the actual family. Induction therefore discharges all difference-sign assumptions.
5. Finite Newton inversion is proved for the actual iterated differences. Their positivity and the actual family's subexponential upper bounds give summability with every geometric weight. The entire Newton series is constructed and interpolates every natural-number value.
6. Its global bound is ||H(z)|| <= a(3N)+C for ||z|| <= N, with a summable 8^r tail. Entirety and growth are proved, not supplied as hypotheses to the final result.
7. Bounded holomorphic uniqueness on Re z > 0 is proved using successive Schwarz division at positive integers, a finite-product bound, and analytic identity. The order-3/4 damping factor is explicit, holomorphic and nonvanishing. No Carlson or Blaschke theorem is assumed.
8. The actual principal complex-power/log branch has proved positive-real normalization and half-plane growth. Analytic continuation to Re z > -m is sufficient; it includes all t-m with t>0. The derivative as t approaches zero from above tends to negative infinity, contradicting continuity of the derivative of the supposed entire extension.

This legitimately replaces the accepted ordinary proof's Pólya–Schur classification and Carlson steps. There is no remaining classification, positivity, growth, interpolation, branch or uniqueness assumption in the final theorem.

## Fresh replay and environment

All 22 frozen author source modules were copied into a new source-only replay, with no author .olean files copied. They were compiled in BUILD_ORDER order, followed by IndependentStatementGuard and IndependentSemanticAudit. All 24 compiler commands exited zero. There were no failed reviewer compiler attempts. Ordinary tactic-style linter warnings are retained in the logs and do not indicate admitted proofs.

Each command used Lean 4.19.0, one thread, a 16 MiB Lean thread stack, disabled asynchronous elaboration, and a 4 GiB OS virtual-memory cap. LEAN_PATH was constructed from only the new replay build directory and the nine pinned official dependency cache directories; no author worktree or unrelated custom project path was present. No dependencies were downloaded or rebuilt during this review.

Mathlib is pinned at c44e0c8ee63ca166450922a373c7409c5d26b00b. All nine dependency commits and clean tracked-source statuses were checked. The previously provisioned official Lean release archive has SHA256 6fe3ce97a58f44e2b3567d455b994eacec5bfe9ae7774f2a573444480ba813fe; 1,484 installed compiler, shared-library and .olean files matched their archive members.

The imported package-source closure contains 2,522 modules, all with matching successful source-build provenance. The two recently built official modules, Complex.Schwarz and SpecialFunctions.Sqrt, were checked against their original source-hash, zero-exit and build-log receipts. The superseded naive analytic discovery record is not used as the dependency closure.

After all commands finished, the complete frozen package, all replay sources, all logs and generated outputs, all nine pins, and 11,698 dependency/compiler/source files were hash-revalidated unchanged.

## Exhaustive kernel-record audit

The audit checks module presence and the exact name, module and declaration kind of every explicit source declaration: 164 author declarations plus six independent guards. It also enumerates every safe kernel declaration originating in the 22 author modules and guard module, including generated safe declarations and anonymous examples.

Results:
- 229 complete safe mathematical types and 229 complete available bodies checked.
- 43,667 distinct constants in their complete transitive logical closure.
- 41,825 available closure bodies and 251 recursor rule bodies checked.
- Only propext, Classical.choice and Quot.sound occur as axioms.
- No sorryAx, unresolved constants, free variables, metavariables, loose bound variables, unsafe or partial mathematical dependency occurs.

The expression traversal follows complete expressions, including projections, binder types, let values and bodies. Recursor rules and inductive/constructor references are included. Full source types, type/body reference inventories, expression hashes, and closure inventories are retained. This is not merely a final-theorem #print axioms check; the union closure covers every safe project declaration.

Compiler artifacts are separately identified rather than silently treated as mathematics: eleven unsafe generated stage records, one partial generated removeIntegerRoots._unsafe_rec record, and one codegen-only closed record. These are not source-declared unsafe/partial mathematics. All thirteen are explicitly inventoried and strictly disjoint from the complete safe logical closure. The safe recursive definition and its mathematical bodies remain included in the audit.

## Evidence and reproduction

The evidence includes all 24 complete compiler logs and per-job records, the unchanged 22 author sources, two independent Lean audit sources, the full mathematical and compiler-artifact inventories, dependency and toolchain provenance, source identities and final hash revalidation. The original author failed elaboration logs are preserved in the author's frozen package; they were not erased or rewritten by this review.

For reproduction, compile the 22 source files in BUILD_ORDER.txt, then IndependentStatementGuard.lean and IndependentSemanticAudit.lean, using only a fresh output directory and the pinned dependency cache on LEAN_PATH. Invoke Lean with -j 1 -s 16384 -DElab.async=false under the 4 GiB OS cap. No network retrieval is part of this procedure. Compiler output is not bundled as proof-source input.

One initial public-copy packaging check correctly rejected an unnormalized HOME path before any archive was produced. That rejected copy and script were retained separately; the normalization was corrected and the public scan rerun. This was not a Lean compilation or mathematical failure.

Public-copy machine paths are normalized to descriptive prefixes. PUBLIC_COPY_MAP.json records original and normalized hashes. Lean source files are unchanged. Build-receipt references use receipt hashes rather than unrelated machine-local directory names. SHA256SUMS.json covers the public evidence files; the archive has a separate SHA256 sidecar.

FULL PASS applies to the exact complete original Problem 34 result described above. It does not establish a new publication or historical-priority claim.
