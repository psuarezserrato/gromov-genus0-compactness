# Mathematical Reference: Mikhail Gromov (1985) Core Lemmas

**Source:** M. Gromov, *"Pseudo holomorphic curves in symplectic manifolds"*, *Inventiones Mathematicae* 82, 307–347 (1985).

---

## 1. Almost Complex Structures and Taming (§0.2)

Let $V$ be a $2n$-dimensional smooth manifold. An almost complex structure on $V$ is a smooth field of endomorphisms $J: TV \to TV$ such that:
$$J^2 = -\mathrm{Id}_{TV}$$

### $\omega$-Taming and Compatibility
Let $\omega$ be a differential 2-form on $V$.
1. **Tamed Structure:** $J$ is said to be *tamed* by $\omega$ (or $\omega$-tamed) if for all non-zero tangent vectors $v \in T_x V \setminus \{0\}$:
   $$\omega(v, Jv) > 0$$
2. **Compatible Structure:** $J$ is *calibrated* or *compatible* with $\omega$ if $J$ is tamed by $\omega$ and the bilinear form:
   $$g_J(v, w) := \omega(v, Jw)$$
   is symmetric: $g_J(v, w) = g_J(w, v)$ for all $v, w \in T_x V$.
   In this case, $g_J$ defines a $J$-invariant Riemannian metric on $V$.
3. **General Symmetrized Metric (for merely tamed $J$):**
   $$g(v, w) = \frac{1}{2}\left(\omega(v, Jw) + \omega(w, Jv)\right)$$
   This metric is strictly positive definite and satisfies $g(Jv, Jw) = g(v, w)$.

---

## 2. Pseudo-Holomorphic Curves and Cauchy-Riemann Operator (§1.1)

Let $(\Sigma, j)$ be a Riemann surface with complex structure $j$. A smooth map $f: \Sigma \to (V, J)$ is called **pseudo-holomorphic** (or $J$-holomorphic) if its differential intertwines $j$ and $J$:
$$df \circ j = J \circ df$$

Equivalently, the Cauchy-Riemann operator vanishes:
$$\bar{\partial}_J f := \frac{1}{2}(df + J \circ df \circ j) = 0$$

### Symplectic Energy
The symplectic area / energy of $f$ over a measurable subset $A \subseteq \Sigma$ is:
$$E(f; A) = \int_A f^* \omega$$
When $f$ is $J$-holomorphic and $J$ is $\omega$-tamed:
$$f^* \omega(v, j v) = \omega(df(v), J(df(v))) \ge 0$$
Hence $f^* \omega$ is a non-negative area form on $\Sigma$, and $E(f; A) \ge 0$ with equality if and only if $f$ is constant on each connected component of $A$.

---

## 3. Bubbling-Off and Gradient Blowup (§1.2)

### The Energy Gap ($\hbar$-Threshold)
**Proposition (Energy Gap):** Let $(V, \omega)$ be a compact symplectic manifold and $J$ an $\omega$-tamed almost complex structure. There exists a universal constant $\hbar = \varepsilon_{sph} > 0$ such that for every non-constant $J$-holomorphic sphere $u: S^2 \to V$:
$$E(u) = \int_{S^2} u^* \omega \ge \hbar$$

*Proof sketch:* By covering $V$ with finitely many contractible Darboux or Euclidean charts and applying epsilon-regularity, a sphere with energy smaller than $\hbar$ has image of diameter smaller than the injectivity radius, hence lies inside a single contractible coordinate ball $U \subset V$. In $U$, the closed 2-form $\omega$ is exact: $\omega|_U = d\alpha$. By Stokes' theorem:
$$E(u) = \int_{S^2} u^* \omega = \int_{S^2} d(u^* \alpha) = \int_{\partial S^2} u^* \alpha = 0$$
Since $E(u) = 0$ implies $u$ is constant, any non-constant sphere must carry energy at least $\hbar$.

### Gradient Rescaling
If a sequence of $J$-holomorphic curves $u_n: \Sigma \to V$ with uniform energy bound $E(u_n) \le B$ has unbounded derivatives $\sup |du_n| \to \infty$, the maximum gradient blow-up points $z_n \to z_0$ can be rescaled by dilations:
$$v_n(z) := u_n(z_n + \lambda_n z), \quad \lambda_n = |du_n(z_n)|^{-1} \to 0$$
By elliptic regularity, $v_n$ converges locally smoothly to a non-trivial pseudo-holomorphic sphere $v_\infty: \mathbb{C} \to V$, which extends smoothly to $S^2 = \mathbb{C} \cup \{\infty\}$ by removable singularity theorems (energy $\ge \hbar$).

---

## 4. Gromov's Compactness Theorem (Inventiones 1985, Theorem 1.2)

Let $(V, \omega)$ be a compact symplectic manifold with $\omega$-tamed $J$. Let $u_n: S^2 \to V$ be a sequence of $J$-holomorphic curves with $E(u_n) \le B$. Then there exists a subsequence $\sigma(n)$ and a cusp-curve / bubble tree $(T, \{u_v\}_{v \in V})$ such that:
1. $u_{\sigma(n)}$ converges to $u_0$ in $C^\infty_{loc}$ away from finitely many bubbling points $Z = \{z_1, \dots, z_k\}$.
2. At each $z_i$, one or more bubble spheres attach, preserving total energy:
   $$\lim_{n \to \infty} E(u_{\sigma(n)}) = \sum_{v \in V(T)} E(u_v)$$
3. The total number of non-constant bubble components $P$ is bounded by $P \le \lfloor B / \hbar \rfloor$.
