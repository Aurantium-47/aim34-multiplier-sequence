# Source correspondence and bounded prior-art audit

Audit date: 22 October 2026. This is a bounded search, not a certification of worldwide priority or an exhaustive survey.

## Original public problem and its date

The primary source is the AIM workshop problem list compiled by Julius Borcea, Petter Brändén, George Csordas and Victor Vinnikov:

https://aimath.org/WWN/polyaschurlax/polyaschurlax.pdf

Problem 34 is on printed page 9. Its formula defines `gamma_k = k^(sqrt(k))` and `f_m(x) = sum_{k>=0} gamma_(k+m) x^k/k!`, and asks whether the shifted sequence is a multiplier sequence for all sufficiently large shifts. The formula was checked against the page image, not inferred from the imperfect text extraction. The square root is the exponent of `k`; it is not a root index or the exponent `k`.

The list prints the shifted sequence beginning at `k=1`, while its exponential generating function starts at `k=0`. This harmless indexing inconsistency is explicitly recorded in the proof. Our theorem excludes all positive real shifts, so either convention gives the same negative answer.

The institutional workshop report identifies the meeting dates as 28 May–1 June 2007:

https://www.aimath.org/pastworkshops/polyaschurlaxrep.pdf

The Stockholm University bibliographic record dates the report to 2007 and records availability from 13 December 2007:

https://su.diva-portal.org/smash/record.jsf?pid=diva2%3A188218

Thus 2007 is supported by primary institutional records. No earlier originating date is claimed. The problem is an explicit numbered question in a recognized public problem list, not a newly named exercise.

## Independent later restatement

Matthew N. Chasse, *Linear Preservers and Entire Functions with Restricted Zero Loci*, doctoral dissertation, University of Hawaiʻi at Mānoa, May 2011, printed page 30, Problem 58:

https://math.hawaii.edu/home/talks/thesis.pdf

This source explicitly cites the AIM list's Problem 34 and asks about `(k+m)^(sqrt(k+m))`, now starting at `k=0`. Its bibliography item [13] identifies the 2007 AIM workshop. The surrounding Questions 59 and 61 concern different parameterized powers; no assertion that these broader questions have been resolved is made here.

The earlier KTH-hosted dissertation URL appeared in search results but returned a missing-file response when directly requested. The accessible university-hosted copy above was used instead; no access restriction was bypassed.

## Classical theorem dependencies

1. Csordas–Forgács, *Multiplier sequences, classes of generalized Bessel functions and open problems*, arXiv:1505.00355v2 (26 August 2015), Definition 3 and Theorem 6, gives the Laguerre–Pólya type-I product and the Pólya–Schur equivalence. The eventual journal reference is J. Math. Anal. Appl. 433 (2016), 1369–1389, DOI 10.1016/j.jmaa.2015.08.047. The proof cites the accessible author preprint, not an unchecked final-typeset identity.

   https://arxiv.org/abs/1505.00355v2

2. Flajolet–Vepstas, *On Differences of Zeta Values*, arXiv:math/0611332v2 (11 July 2007), Corollary 1 proof, printed pages 10–11, explicitly states the sufficient Carlson half-plane uniqueness theorem used here. It gives the bound `|g(s)| < C exp(A|s|)` throughout the right half-plane with `A < pi`, together with vanishing at the nonnegative integers. It refers to Hardy's lectures, pp. 188–191, and Titchmarsh, section 5.81. The proof here verifies the stronger all-small-positive-type bound uniformly on that half-plane.

   https://algo.inria.fr/flajolet/Publications/FlVe07.pdf

These classical results are credited dependencies, not discoveries of this note. The local normal-convergence, binomial-inversion and branch-singularity arguments are supplied in full.

## Later literature checked and limitations

The 2015 Csordas–Forgács paper is particularly relevant because its abstract emphasizes multiplier sequences interpolated by functions that are not entire. Its complete accessible text was checked for the target formula, shifted-sequence discussion, Carlson's theorem and Newton interpolation. It does not state a resolution of AIM Problem 34. Its logarithmic positive result instead concerns `(H_(n+2)−EulerGamma)/n!`, and its discussion of `log(n+2)/n!` has an essential factorial denominator. It does not imply that the non-entire interpolants in the present proof are multiplier sequences. The theorem here does not exclude arbitrary non-entire interpolants: the root limit, uniform half-plane growth and exact uniqueness hypotheses matter.

The 2011 dissertation's Proposition 49 attributes forward-difference positivity for nondecreasing positive multiplier sequences to Craven–Csordas, *The Gauss–Lucas theorem and Jensen polynomials*, Trans. Amer. Math. Soc. 278 (1983), 415–429. This positivity principle is therefore not claimed as new. Our proof derives the particular positivity needed directly from the Pólya–Schur product, avoiding the extra nondecreasing hypothesis for small real shifts.

Targeted public searches combined the original problem number, AIM workshop title, Chasse Problem 58, the literal radical-power formula, “multiplier sequences” with “Carlson”, and “multiplier sequences” with “Newton series” or “subexponential”. They located the original problem and Chasse's restatement, but no exact positive or negative resolution of this particular question. Formula-indexing quality is poor: many results were irrelevant, so failure to find a later resolution is weak evidence, not proof of novelty. No exhaustive citation-network or all-language search was performed. No universal claim that the problem remained open until this note is warranted.

## Scope of the conclusion

The manuscript gives a full negative answer to the stated eventual-shift question, conditional only on its displayed proof being correct. Its analytic theorem rules out every positive real shift. The eight exact finite-difference certificates illustrate particular shifts and do not replace the all-shifts proof. They are one project, not eight distinct conjectures. There is no result here about all of Chasse's adjacent questions, the Riemann xi-function, or the distribution of every zero of the generating function.

The status of an independent mathematical review is separate from this source audit. Neither an exact computation nor such a review certifies global historical priority.
