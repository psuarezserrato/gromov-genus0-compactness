# Sample Informal Mathematical Text: Gromov Compactness for Genus 0 Curves

### Theorem (Gromov Compactness for Pseudo-holomorphic Spheres)
Let $(M, \omega)$ be a compact, boundaryless symplectic manifold equipped with a smooth $\omega$-compatible almost complex structure $J$.
Let $u_n: S^2 \to M$ be a sequence of pseudo-holomorphic spheres satisfying the Cauchy-Riemann equation $\bar{\partial}_J u_n = 0$ with a uniform energy bound:
$$E(u_n) = \int_{S^2} u_n^* \omega \le B < \infty$$
for all $n \in \mathbb{N}$.

Then there exists a subsequence $\sigma: \mathbb{N} \to \mathbb{N}$ and a stable rooted sphere tree $T = (V, E)$ with curves $u_v: S^2 \to M$ ($v \in V$) such that:
1. $u_{\sigma(n)}$ converges to $u_v$ in $C^\infty_{loc}$ away from a finite set of nodal points.
2. The total energy is preserved:
   $$\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V} E(u_v)$$
3. The number of components $|V|$ is bounded by $|V| \le 2 \lfloor B / \hbar \rfloor - 2$.
