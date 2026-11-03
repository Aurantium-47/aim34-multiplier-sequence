# A negative answer to AIM 2007 Problem 34

## Scope and status

This note addresses Problem 34 in the 2007 AIM workshop list *Pólya–Schur–Lax Problems: Hyperbolicity and Stability Preservers*, compiled by Julius Borcea, Petter Brändén, George Csordas and Victor Vinnikov. The same question is restated as Problem 58 on printed page 30 of Matthew N. Chasse's 2011 dissertation. The theorem below is an author proof pending independent review. No formal proof-assistant verification or global-priority claim is made.

The original sequence and its exponential generating functions are

\[
 \gamma_k=k^{\sqrt{k}}\quad(k\geq1),\qquad
 f_m(z)=\sum_{k\geq0}\frac{(k+m)^{\sqrt{k+m}}}{k!}z^k.
\]

The question asks whether the shifted sequence is a multiplier sequence when the positive integer shift is sufficiently large. The square root is in the exponent. The AIM list prints the shifted sequence starting at index 1, whereas its generating function starts at index 0. Chasse's restatement starts at index 0. The theorem covers every positive real shift, so shifting either indexing convention by one does not alter the negative answer.

**Theorem.** For every real number \(m>0\), the sequence

\[
 \bigl\{(n+m)^{\sqrt{n+m}}\bigr\}_{n\geq0}
\]

is not a classical multiplier sequence. In particular, no positive integer shift in AIM Problem 34 works.

A classical multiplier sequence \((a_n)\) is a real sequence such that the diagonal map \(\sum c_nz^n\mapsto\sum a_nc_nz^n\) preserves real-rooted real polynomials (allowing the zero polynomial).

## 1. Two classical dependencies

We use the following standard forms of two classical theorems, not new results of this note.

**Pólya–Schur theorem, positive-coefficient form.** If \(a_n>0\) and \((a_n)\) is a classical multiplier sequence, then

\[
 F(z)=\sum_{n\geq0}a_n\frac{z^n}{n!}
      =a_0e^{\sigma z}\prod_j(1+\alpha_jz),
 \qquad \sigma\geq0,\quad \alpha_j>0,\quad\sum_j\alpha_j<\infty.
 \tag{1}
\]

The product may be finite or empty. There is no factor \(z^r\), because \(F(0)=a_0>0\). The positive-coefficient assumption selects the orientation with negative zeros and nonnegative exponential parameter. A convenient accessible source is Csordas–Forgács, arXiv:1505.00355v2, Definition 3 and Theorem 6.

**Carlson uniqueness theorem, sufficient half-plane form.** Suppose \(g\) is holomorphic on a neighborhood of the closed right half-plane and

\[
 |g(z)|\leq C e^{A|z|}\qquad(\Re z\geq0)
\]

for constants \(C<\infty\) and \(0\leq A<\pi\). If \(g(n)=0\) for every integer \(n\geq0\), then \(g\) is identically zero on the right half-plane. This sufficient version is explicitly stated in the proof of Corollary 1 of Flajolet–Vepstas, *On Differences of Zeta Values*, arXiv:math/0611332v2, printed pages 10–11; that source refers to Hardy and Titchmarsh for the classical theorem.

The argument below supplies the uniform half-plane growth hypothesis, not merely growth along the positive real axis.

## 2. Forward differences forced by the multiplier assumption

Fix \(m>0\), and write

\[
 a_n=(n+m)^{\sqrt{n+m}}.
\]

All \(a_n\) are positive, \(a_n\geq1\) for all sufficiently large \(n\), and

\[
 \frac{\log a_n}{n}=\frac{\sqrt{n+m}\log(n+m)}{n}\longrightarrow0.
 \tag{2}
\]

Consequently, for every \(\varepsilon>0\) there is \(C_\varepsilon>0\) such that \(a_n\leq C_\varepsilon e^{\varepsilon n}\) for all \(n\). In particular \(F\) is entire and

\[
 F(r)\leq C_\varepsilon\exp(e^\varepsilon r),\qquad r\geq0.
 \tag{3}
\]

Conversely, for a sufficiently large fixed integer \(N_0\),

\[
 F(r)\geq\sum_{n\geq N_0}\frac{r^n}{n!}
       =e^r-\sum_{n<N_0}\frac{r^n}{n!}.
\]

The subtracted polynomial is \(o(e^r)\). Using (3) and then letting \(\varepsilon\downarrow0\) therefore gives

\[
 \lim_{r\to\infty}\frac{\log F(r)}r=1.
 \tag{4}
\]

Assume, for contradiction, that \((a_n)\) is a multiplier sequence, and apply (1). For every \(r>0\),

\[
 0\leq\frac{\log(1+\alpha_jr)}r\leq\alpha_j.
\]

Each term tends to zero as \(r\to\infty\). Since \(\sum_j\alpha_j<\infty\), dominated convergence for the summable series yields

\[
 \frac1r\sum_j\log(1+\alpha_jr)\longrightarrow0.
\]

Equations (1) and (4) force \(\sigma=1\). Thus

\[
 e^{-z}F(z)=a_0\prod_j(1+\alpha_jz)
\]

has nonnegative Taylor coefficients. For an infinite product this follows from locally uniform convergence of its finite products, whose coefficients are nonnegative. Define

\[
 d_r=\Delta^ra_0:=\sum_{j=0}^r(-1)^{r-j}\binom rj a_j.
 \tag{5}
\]

Multiplying the absolutely convergent exponential series gives

\[
 e^{-z}F(z)=\sum_{r\geq0}d_r\frac{z^r}{r!},
 \qquad d_r\geq0.
 \tag{6}
\]

Finite binomial inversion gives, for every integer \(N\geq0\),

\[
 a_N=\sum_{r=0}^N\binom Nr d_r.
 \tag{7}
\]

For an integer \(K\geq2\) and \(r\geq1\), all terms in (7) with \(N=Kr\) are nonnegative, whence

\[
 0\leq d_r\leq\frac{a_{Kr}}{\binom{Kr}r}
             \leq\frac{a_{Kr}}{K^r}.
 \tag{8}
\]

The last inequality follows from

\[
 \binom{Kr}r=\prod_{j=0}^{r-1}\frac{Kr-j}{r-j}\geq K^r.
\]

For each fixed \(K\), equation (2) implies \(a_{Kr}^{1/r}\to1\). Taking upper limits in (8) gives \(\limsup_{r\to\infty}d_r^{1/r}\leq1/K\). As \(K\) is arbitrary,

\[
 \limsup_{r\to\infty}d_r^{1/r}=0.
 \tag{9}
\]

Zero values of \(d_r\) cause no difficulty; their \(r\)-th roots are zero.

## 3. An entire Newton interpolant of minimal exponential type

Consider

\[
 H(z)=\sum_{r=0}^{\infty}d_r\binom zr,
 \qquad \binom zr=\frac{z(z-1)\cdots(z-r+1)}{r!},\quad\binom z0=1.
 \tag{10}
\]

For every \(q\in(0,1)\), equation (9) gives a finite constant \(C_q\) with \(d_r\leq C_qq^r\) for every \(r\geq0\). For \(R=|z|\),

\[
 \left|\binom zr\right|\leq\frac{R(R+1)\cdots(R+r-1)}{r!}
                         =\frac{(R)_r}{r!}.
\]

The convention \((R)_0=1\) applies, including \(R=0\). The binomial series therefore gives

\[
 |H(z)|\leq C_q\sum_{r\geq0}\frac{(R)_r}{r!}q^r
          =C_q(1-q)^{-R}.
 \tag{11}
\]

The same bound with \(R\) fixed on a compact disk proves uniform absolute convergence there, so \(H\) is entire. Since \(-\log(1-q)\downarrow0\) as \(q\downarrow0\), (11) proves that, for each \(\eta>0\),

\[
 |H(z)|\leq C_\eta e^{\eta|z|}\qquad(z\in\mathbb C).
 \tag{12}
\]

At a nonnegative integer \(N\), the Newton series terminates at \(r=N\). Equation (7) gives \(H(N)=a_N\).

## 4. Carlson uniqueness and the branch-point contradiction

Let

\[
 \Omega_m=\mathbb C\setminus(-\infty,-m],\qquad
 h_m(z)=\exp\bigl(\sqrt{z+m}\,\operatorname{Log}(z+m)\bigr),
 \tag{13}
\]

where both the logarithm and the square root are principal branches. This function is holomorphic on the connected slit domain \(\Omega_m\), which contains an open neighborhood of the closed right half-plane. On that half-plane put \(w=z+m\). Then \(|w|\geq m\), \(|w|\leq|z|+m\), and \(|\arg w|\leq\pi/2\). Hence a constant \(B_m\) exists such that

\[
 |\operatorname{Log} w|\leq B_m+\log(1+|z|),
\]

and therefore

\[
 |h_m(z)|\leq
 \exp\!\left(\sqrt{|z|+m}\,[B_m+\log(1+|z|)]\right).
 \tag{14}
\]

The exponent on the right is \(o(|z|)\) as \(|z|\to\infty\), uniformly in the closed right half-plane. Consequently, for every \(\eta>0\) there is \(D_{m,\eta}<\infty\) with

\[
 |h_m(z)|\leq D_{m,\eta}e^{\eta|z|}\qquad(\Re z\geq0).
 \tag{15}
\]

We have \(h_m(N)=a_N=H(N)\) for every nonnegative integer \(N\). By (12) and (15), the holomorphic difference \(H-h_m\) satisfies the stated Carlson bound, for example with \(A=1<\pi\). Carlson's theorem gives equality on the right half-plane. The identity theorem then gives \(H=h_m\) throughout \(\Omega_m\).

For \(t>0\), this equality implies

\[
 H(t-m)=t^{\sqrt t},\qquad
 H'(t-m)=t^{\sqrt t}\frac{\log t+2}{2\sqrt t}.
 \tag{16}
\]

As \(t\downarrow0\), \(\sqrt t\log t\to0\), so \(t^{\sqrt t}\to1\). But the derivative on the right of (16) tends to \(-\infty\). This is impossible for an entire \(H\): its derivative is continuous, hence bounded in a neighborhood of the finite point \(-m\).

This contradiction proves the theorem for every real \(m>0\). In particular it answers the original eventual-positive-integer-shift question negatively. \(\square\)

## 5. Exact finite certificates, supplementary to the proof

The analytic proof covers every positive real shift and does not depend on a finite computation. The accompanying standard-library Python verifier independently encloses the finite differences (5) for the following integer shifts and orders:

\[
 (m,r)=(1,23),(2,27),(3,31),(5,37),(10,47),(20,63),(50,97),(100,137).
\]

It verifies that every upper endpoint is strictly negative, using only integer arithmetic and outward-rounded dyadic intervals. Each such negative difference independently contradicts (6) for that particular shift. These are not asserted to be the first negative differences, nor are they claimed to directly exhibit a particular Jensen polynomial.

The enclosure method is documented in `certificate_method.md`; both the dyadic endpoints and convenient exact decimal-rational endpoints are recorded by `verify.py`. The calculation is repeated at two precisions. No floating-point root approximation is used.

## References

1. J. Borcea, P. Brändén, G. Csordas and V. Vinnikov, *AIM Workshop “Pólya–Schur–Lax Problems: Hyperbolicity and Stability Preservers”: A List of Open Problems* (2007), Problem 34, printed p. 9. https://aimath.org/WWN/polyaschurlax/polyaschurlax.pdf
2. M. N. Chasse, *Linear Preservers and Entire Functions with Restricted Zero Loci*, doctoral dissertation, University of Hawaiʻi at Mānoa, May 2011, Problem 58, printed p. 30. https://math.hawaii.edu/home/talks/thesis.pdf
3. G. Csordas and T. Forgács, *Multiplier sequences, classes of generalized Bessel functions and open problems*, J. Math. Anal. Appl. 433 (2016), 1369–1389; arXiv:1505.00355v2 (26 August 2015), Definition 3 and Theorem 6. https://arxiv.org/abs/1505.00355v2
4. P. Flajolet and L. Vepstas, *On Differences of Zeta Values*, arXiv:math/0611332v2 (11 July 2007), Corollary 1 and its proof, printed pp. 10–11. https://algo.inria.fr/flajolet/Publications/FlVe07.pdf
