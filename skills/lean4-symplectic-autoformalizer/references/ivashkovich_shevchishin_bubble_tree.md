# Mathematical Reference: Ivashkovich & Shevchishin (1999) Bubble Trees

**Source:** S. Ivashkovich, V. Shevchishin, *"Complex Curves in Almost-Complex Manifolds and Meromorphic Hulls"*, arXiv:math/9912046 (1999).

---

## 1. Area Bounds and Monotonicity for Almost-Complex Manifolds (§1)

Ivashkovich and Shevchishin provide foundational analytic tools for curves in non-integrable almost-complex manifolds $(M, J)$:

### Local Isoperimetric Inequality and Area Bounds
Let $(M, J)$ be an almost complex manifold equipped with a Hermitian metric $g$. For any $J$-complex curve $C \subset M$:
$$\mathrm{Area}(C \cap B_r(x)) \ge c r^2$$
for $r \le r_0$, where $c > 0$ and $r_0 > 0$ depend only on the bounds on $J$ and the geometry of $M$.
This monotonicity formula guarantees that non-trivial complex curve components cannot have arbitrarily small non-zero area inside balls centered on the curve.

---

## 2. Tree-Like Connectedness of Genus 0 Bubbles (§2)

A crucial theorem of Ivashkovich-Shevchishin establishes the dual graph topology for limits of genus 0 curves:

### Dual Graph Theorem
Let $u_n: \mathbb{CP}^1 \to M$ be a sequence of pseudo-holomorphic spheres of bounded energy $E(u_n) \le B$. Then the limit object in the sense of cusp-curves has a dual graph $G = (V, E)$ that is a **tree** (connected and acyclic):
1. **No Loops (Acyclicity):** If $G$ contained a cycle, the topological genus of the approximating curves would be at least 1, contradicting the assumption that the domain is $\mathbb{CP}^1$ (genus 0).
2. **Simple Nodes:** All singular nodal intersections between components $u_v$ and $u_w$ are simple normal crossings with $u_v(z_{vw}) = u_w(z_{wv})$.
3. **Distinct Node Positions:** On any single component $v$, all incident node positions $\{z_{vw} : w \sim v\}$ are pairwise distinct points in $\mathbb{CP}^1$.

---

## 3. Stability and Automorphism Finiteness

### Constant Ghost Components
A component $v \in V$ is called a **ghost** if $u_v: \mathbb{CP}^1 \to M$ is constant ($E(u_v) = 0$).
- In Gromov's bubbling construction, ghost components arise when multiple concentration clusters occur on a component with diverging relative coordinates.
- **Stability Condition:** A ghost component $v$ must have degree $\mathrm{deg}(v) \ge 3$ (or $\mathrm{deg}(v) + k_v \ge 3$ in the presence of $k_v$ marked points).
- **Automorphism Group:** An automorphism of a component is a biholomorphic map $\phi \in \mathrm{Aut}(\mathbb{CP}^1) \cong \mathrm{PSL}(2, \mathbb{C})$ fixing the nodal points and marked points and satisfying $u_v \circ \phi = u_v$.
  - For a non-constant component, the fiber over distinct points is finite, so $\mathrm{Aut}(u_v)$ is finite.
  - For a constant component, an automorphism fixes all nodal points. Since a Möbius transformation fixing $\ge 3$ distinct points is the identity, $\mathrm{deg}(v) \ge 3$ guarantees that $\mathrm{Aut}(T)$ is finite.

### Ghost Count Bound
If $P$ is the number of non-constant components and $G$ is the number of constant ghost components in a tree with $|V| > 1$:
$$3G + P \le 2(|V| - 1) = 2(P + G - 1) \implies G \le P - 2$$
Consequently:
$$|V| = P + G \le 2P - 2$$
Since each non-constant component satisfies $E(u_v) \ge \hbar$, we obtain:
$$P \le \lfloor B / \hbar \rfloor \implies |V| \le 2 \lfloor B / \hbar \rfloor - 2$$
