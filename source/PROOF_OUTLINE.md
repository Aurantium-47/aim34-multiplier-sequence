# AIM 2007 Problem 34: full formalization route

## Exact scope
For every real m>0, the actual coefficientwise diagonal operator with multipliers
(n+m)^(sqrt(n+m)), n>=0, does not preserve all real-rooted real polynomials.
Zero polynomials are allowed as input and output in the preserver definition.
The result also explicitly covers the one-indexed sequence printed by AIM and
all positive integer shifts in Chasse's restatement. There is no uniform finite
counterexample-degree claim and no global novelty or publication claim.

## Original sources
- Borcea, Brändén, Csordas and Vinnikov, AIM 2007 problem list, Problem 34,
  printed page 9: https://aimath.org/WWN/polyaschurlax/polyaschurlax.pdf
  PDF SHA256 526a5a9ed0e4cb417034d32b9b5bb57610659b21123f6f4dce3dedde9731df36.
- M. N. Chasse, 2011 dissertation, Problem 58, printed page 30:
  https://math.hawaii.edu/home/talks/thesis.pdf
  PDF SHA256 bfb96ee15c6e1f9ef864b55f322dabb3277fbb8169eb6155cf7d73cc53945ff3.

The AIM displayed sequence begins at 1 while its generating function begins at
0. The all-positive-real-shift theorem covers both conventions. The radical is
in the exponent. The earlier accepted ordinary proof is preserved unchanged;
its SHA256 is 59d52912eae6ca7f5152b741ae2aa56b00b36f0ed72af5d2aa470927253f3e35.
This formalization replaces its classification and Carlson steps, rather than
assuming those classical statements through new axioms.

## Finite algebra and sign invariant
1. The actual preserver applied to (1+X)^N gives every finite Jensen polynomial.
2. A root-product logarithmic-derivative argument proves derivative closure.
   For the degree-padded polar operator (X+1)p'−M p with degree p<=M, a nonreal
   zero forces M−degree p=−sum (r+1)^2/|z−r|^2. Thus the only possible exceptional
   output is identically zero. Constants, degree drops and multiplicities remain.
3. Exact coefficient identities therefore propagate Jensen real-rootedness under
   shifts and forward difference. No finite Jensen sufficiency is used.
4. Quadratic Jensen polynomials give adjacent log-concavity. A nonnegative
   real-rooted polynomial with positive constant and zero linear coefficient is
   constant: otherwise all roots are strictly negative and its logarithmic
   derivative at zero is positive. This supplies the essential zero-tail and
   interval-support argument, not an invalid inference from log-concavity alone.
5. A strict drop in any nonnegative, log-concave, gap-free difference sequence
   forces a bounded tail. Bounded r-th differences bound the original sequence
   by a polynomial of degree r, with unrestricted initial values absorbed.
6. The actual family grows faster than every polynomial. Induction thus proves
   all iterated forward differences nonnegative, at every starting index.

## Analytic contradiction
7. Finite Newton inversion is proved for the actual forward differences.
   Positivity and the actual family's subexponential bounds imply weighted
   summability for every base. The resulting Newton series is entire and
   interpolates the sequence at every natural number.
8. Its uniform complex growth bound is |H(z)|<=a(3N)+C for |z|<=N. The low-index
   estimate uses binomial(3N,r); the tail bound 8^r is absorbed by proved weighted
   summability. No entire-interpolant or growth bridge is an assumption.
9. A bounded holomorphic function on Re z>0 vanishing at every positive integer
   is zero. The proof constructs removable Schwarz quotients, iterates finite
   half-plane factors, bounds their squared product on an open complex lens by
   1/(2N+1), and applies the identity theorem.
10. Explicit exp(−A(z+1)^(3/4)) damping applies this uniqueness result to H minus
    exp((z+m)^(1/2) Log(z+m)). Principal-branch holomorphy, positive-real
    normalization and growth bounds are proved. Continuation uses the convex
    shifted half-plane Re z>−m, so no unstated slit-connectivity claim is needed.
11. At the boundary, the real derivative is
    exp(sqrt(t) log(t)) (log(t)+2)/(2 sqrt(t)), which tends to minus infinity as
    t tends to zero from above. This contradicts continuity of an entire
    extension's derivative. All conditions are discharged for each m>0.

## Reuse and limits
Five generic root-product lemmas and the root-product definition were reused
from the independently accepted CGV Bell/Laguerre sources, with namespace and
imports adapted. The original BellRoots.lean SHA256 is
c338f65cb0d7cb059004e10da8323baf822a485c836252a25ace90d1bae5b3b3.
The AIM closure does not import the Bell or Laguerre theorem as an assumption.
The full target has now been independently replayed and semantically audited.
See independent_review/INDEPENDENT_REVIEW.md for the exact acceptance scope.
