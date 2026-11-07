# Technical Investigation & Analysis: Contract A02 (`bochner_differential_inequality`)

**Explorer Agent**: `teamwork_explorer_p6m1_2`  
**Phase**: Phase 6 Local Analysis (Milestone 1: A01–A03)  
**Target Declaration**: `GromovCompactness.Analysis.bochner_differential_inequality`  
**Primary File**: `GromovCompactness/Analysis/Bochner.lean`  
**Target Milestone**: Phase 6 Milestone 1 (Contracts A01, A02, A03)

---

## 1. Exact Lean 4 Type Signature and Current Proof Status

### 1.1 Type Signature

In `GromovCompactness/Analysis/Bochner.lean` (lines 194–205):

```lean
theorem bochner_differential_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
    ∀ (u : CP1 → M),
      JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
      ∀ (w : ℂ),
        -b * (riemannianEnergyDensity I u (stereo_chart.symm w))^2 -
          c * (riemannianEnergyDensity I u (stereo_chart.symm w)) ≤
        laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w
```

### 1.2 Proof Body and Current `sorry` Status

The proof body of `bochner_differential_inequality` in `Bochner.lean` (lines 206–211) is:

```lean
  rcases bochner_curvature_term_bound (M := M) I with ⟨b, c, hb, hc, h_decomp⟩
  refine ⟨b, c, hb, hc, ?_⟩
  intro u hu w
  rcases h_decomp u hu w with ⟨hessNorm, curvTerm, h_weitz, h_curv⟩
  exact bochner_inequality_pointwise_of_decomposition h_weitz h_curv
```

1. **Direct `sorry` audit**: `bochner_differential_inequality` itself contains **zero direct `sorry`**.
2. **Intermediate lemma status**:
   - `bochner_inequality_pointwise_of_decomposition` (lines 180–187): **Proved** with zero `sorry` (standard linear arithmetic via `linarith` and `sq_nonneg`).
   - `bochner_curvature_term_bound` (lines 161–176): Contains **direct `sorry`** on line 176.
   - `contDiff_energy_density_chart` (lines 147–154): Contains **direct `sorry`** on line 154.
3. **Transitive Axiom Census**: Because `bochner_differential_inequality` calls `bochner_curvature_term_bound`, it transitively depends on `sorryAx`. The compiler confirms:
   - `lake build GromovCompactness.Analysis.Bochner` yields:
     - `warning: Bochner.lean:147:6: declaration uses 'sorry'` (`contDiff_energy_density_chart`)
     - `warning: Bochner.lean:161:8: declaration uses 'sorry'` (`bochner_curvature_term_bound`)

---

## 2. Geometric Representation: Intrinsic vs. Coordinate Objects

The formalization represents the underlying geometric data across four modules (`Target.lean`, `Sphere.lean`, `Energy.lean`, `Bochner.lean`):

### 2.1 The Target Geometric Objects
- **Almost-Complex Structure $J$**:
  In `GromovCompactness/Geometry/Target.lean`:
  `ClosedTameTarget.J : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x`
  with condition `J_sq : ∀ x v, J x (J x v) = -v`.
  Smoothness is given chartwise:
  `J_smooth : ∀ (x : M), ContDiffOn ℝ ∞ (J_chart I J x) (extChartAt I x).target`.
- **Symplectic 2-Form $\omega$**:
  `ClosedTameTarget.«ω» : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`
  skew-symmetric (`ω_skew`), non-degenerate (`ω_nondegenerate`), chartwise $C^\infty$ (`ω_smooth`), and closed (`ω_closed`).
- **Riemannian Metric $g$**:
  `ClosedTameTarget.metric I x v w := (1 / 2 : ℝ) * (tgt.«ω» x v (tgt.J x w) + tgt.«ω» x w (tgt.J x v))`.
  Proved properties in `Target.lean`:
  - `metric_symm`: $g(v, w) = g(w, v)$
  - `metric_pos_def`: $v \ne 0 \implies g(v, v) > 0$
  - `metric_J_invariant`: $g(Jv, Jw) = g(v, w)$.

### 2.2 The Domain Geometric Objects ($\mathbb{CP}^1$)
- **Riemann Sphere $\mathbb{CP}^1$**:
  Modeled as the round unit sphere in $\mathbb{R}^3$:
  `CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
  with model with corners `I_CP1 := 𝓡 2` (`EuclideanSpace ℝ (Fin 2)`).
- **Domain Complex Structure $j_{\mathbb{CP}^1}$**:
  `J_CP1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)` is multiplication by $i$ under the isometric equivalence `c_equiv_e2 : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2)`.
  The canonical orthonormal basis vectors are `e1 = !₂[1, 0]` and `e2 = !₂[0, 1]`.
- **Stereographic Chart**:
  `stereo_chart : PartialHomeomorph CP1 ℂ` with source $\{north\_pole\}^c$ and target $\mathbb{C}$.

### 2.3 Energy Density and Laplacian
- **Pointwise Riemannian Energy Density**:
  In `Energy.lean` (lines 95–97):
  ```lean
  noncomputable def riemannianEnergyDensity (u : CP1 → M) (z : CP1) : ℝ :=
    (1 / 2 : ℝ) * (ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) +
                  ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2))
  ```
  This is the norm-squared of the differential $du_z$ with respect to the round spherical metric on $T_z \mathbb{CP}^1$.
- **Laplacian $\Delta e$**:
  In `Bochner.lean` and `Monotonicity.lean`:
  ```lean
  noncomputable def laplacian2D (e : ℂ → ℝ) (z : ℂ) : ℝ :=
    (iteratedFDeriv ℝ 2 e z) ![1, 1] + (iteratedFDeriv ℝ 2 e z) ![Complex.I, Complex.I]
  ```
  This is the **flat Euclidean 2D Laplacian** $\Delta_{\mathbb{C}} = \frac{\partial^2}{\partial x^2} + \frac{\partial^2}{\partial y^2}$ on $\mathbb{C}$.

---

## 3. Impact of COMPLETION_PLAN Tasks P0-3, P0-4, and P0-5

### 3.1 Task P0-3 (Target Smoothness and Closedness)
- **Problem in Baseline**: Earlier drafts had `ω_closed : Prop` and `J_smooth : Prop` as unconstrained propositions with no mathematical meaning.
- **Current State**: Phase 5 Milestone 2 successfully resolved P0-3. In `Target.lean`:
  - `ω_smooth` specifies chartwise $C^\infty$ smoothness in every chart.
  - `ω_closed` specifies the vanishing of the cyclic sum of directional Fréchet derivatives in charts ($d\omega = 0$).
  - `J_smooth` specifies chartwise $C^\infty$ smoothness in every chart.
- **Consequence for A02**: Because $M$ is compact (`CompactSpace M`) and $J, \omega, g$ are smooth, all chartwise derivatives of $J$ and the metric tensor $g$ ($DJ, D^2J, Dg, D^2g$) are continuous functions on compact domains, and therefore **uniformly bounded** by target constants $K_1, K_2, K_3, K_4 < \infty$. These supply the uniform constants $b, c \ge 0$.

### 3.2 Task P0-4 (Alignment between A01 and A02)
- **Problem in Baseline**: `scalar_mean_value_inequality` (A01) assumed $\Delta e \ge -b e^2$, whereas `bochner_differential_inequality` (A02) provided $\Delta e \ge -b e^2 - c e$. They could not be composed without an algebraic mismatch.
- **Current State**: In `Monotonicity.lean` (lines 78–87), `scalar_mean_value_inequality` has already been generalized:
  ```lean
  theorem scalar_mean_value_inequality
      (b : ℝ) (hb : 0 ≤ b) (c : ℝ := 0) (hc : 0 ≤ c := by norm_num) :
      ∃ (η C : ℝ), 0 < η ∧ 0 < C ∧
      ∀ (r : ℝ) (hr : 0 < r) (e : ℂ → ℝ),
        ...
        (∀ z ∈ Metric.ball (0 : ℂ) r, -b * (e z)^2 - c * (e z) ≤ laplacian2D e z) → ...
  ```
  And in `EpsilonRegularity.lean` (lines 77–78):
  ```lean
  obtain ⟨b, c, hb, hc, h_boch⟩ := bochner_differential_inequality (M := M) I
  obtain ⟨η, C, hη, hC, h_smv⟩ := scalar_mean_value_inequality b hb c hc
  ```
- **Consequence for A02**: The interfaces are now syntactically aligned! The constants $(b, c)$ from `bochner_differential_inequality` plug directly into `scalar_mean_value_inequality`.

### 3.3 Task P0-5 (Density Convention and Conformal Factor)
- **Problem in Baseline**:
  In `Bochner.lean`, the energy density being differentiated is `riemannianEnergyDensity I u (stereo_chart.symm w)`.
  This is the density measured with respect to the **spherical round metric** on $T \mathbb{CP}^1$, but differentiated with respect to the **flat Euclidean Laplacian** on $\mathbb{C}$.
  The spherical round metric in stereographic coordinates is conformal to the Euclidean metric:
  $$g_{S^2} = \lambda(w)^2 |dw|^2, \quad \lambda(w) = \frac{2}{1 + |w|^2}.$$
  Consequently, the spherical energy density $e_{S^2}(w)$ and the Euclidean energy density $e_{\mathrm{euc}}(w) = \frac{1}{2}|d(u \circ \sigma^{-1})|^2$ are related by:
  $$e_{S^2}(w) = \frac{1}{\lambda(w)^2} e_{\mathrm{euc}}(w) = \frac{(1 + |w|^2)^2}{4} e_{\mathrm{euc}}(w).$$
- **Key Analytical Insight**:
  1. For the Euclidean energy density $e_{\mathrm{euc}}$ on a flat domain $\mathbb{C}$, the Bochner inequality is **purely quadratic**:
     $$\Delta_{\mathbb{C}} e_{\mathrm{euc}} \ge - b (e_{\mathrm{euc}})^2 \quad (\text{i.e. } c = 0).$$
     There is no linear term because the Gaussian curvature of flat $\mathbb{C}$ is zero!
  2. For the spherical energy density $e_{S^2}$, the Leibniz rule gives:
     $$\Delta_{\mathbb{C}} e_{S^2} = \Delta_{\mathbb{C}}(\rho \cdot e_{\mathrm{euc}}) = \rho \Delta e_{\mathrm{euc}} + 2 \nabla \rho \cdot \nabla e_{\mathrm{euc}} + (\Delta \rho) e_{\mathrm{euc}},$$
     where $\rho(w) = \frac{(1+|w|^2)^2}{4}$. Notice that $\Delta \rho(w) = 2 + 4 |w|^2$.
     On the entire plane $\mathbb{C}$, as $|w| \to \infty$, $\rho$ and $\Delta \rho$ grow quadratically/quarticly.
  3. However, since $u : \mathbb{CP}^1 \to M$ is smooth on the **compact** sphere $\mathbb{CP}^1$, the function $z \mapsto \text{riemannianEnergyDensity}(u)(z)$ is a smooth function on $S^2$.
     When expressed in stereographic coordinates $w$, as $w \to \infty$, inversion to coordinates $\zeta = 1/w$ shows that $\Delta_w (e_{S^2}(w)) = |\zeta|^4 \Delta_\zeta (e_{S^2}(\zeta^{-1})) \to 0$ as $|w| \to \infty$. Thus $\Delta_w e_{S^2}$ remains globally bounded!
  4. In `scalar_mean_value_inequality`, the integral is $\int_{B_r} e(w) dw$, while in `epsilon_regularity`, the hypothesis is `energyMeasure I u (disk_at a r) < ε_reg`, where:
     $$\text{energyMeasure}(u; \text{disk\_at } a r) = \int_{B_r(a)} e_{S^2}(w) \cdot \lambda(w)^2 dw = \int_{B_r(a)} e_{\mathrm{euc}}(w) dw.$$
     The spherical factor $\lambda(w)^2 = \text{sphericalJacobian}(w)$ exactly cancels the $\lambda(w)^{-2}$ in the density!
     **Therefore, the integrated energy measure is IDENTICAL to the Euclidean integral of the Euclidean density!**

---

## 4. Mathematical Route: Step-by-Step Derivation

### 4.1 Coordinate Computation for Cauchy-Riemann Maps

Let $u : \mathbb{CP}^1 \to M$ be a $J$-holomorphic curve. Let $w = s + it \in \mathbb{C}$, and let $f = u \circ \sigma^{-1} : \mathbb{C} \to M$.
In local coordinates on $M$, $f$ is a map into $\mathbb{R}^{2n}$.
The Cauchy-Riemann equation is:
$$\partial_s f + J(f) \partial_t f = 0 \iff \partial_s f = - J(f) \partial_t f \quad\text{and}\quad \partial_t f = J(f) \partial_s f.$$

#### Step 1: Cancellation of Second Derivatives in the Tension Field $\Delta f$
Differentiating with respect to $s$ and $t$:
$$\partial_s^2 f = - J(f) \partial_s \partial_t f - (DJ(f) \cdot \partial_s f) \partial_t f,$$
$$\partial_t^2 f = J(f) \partial_t \partial_s f + (DJ(f) \cdot \partial_t f) \partial_s f.$$
Since mixed partial derivatives commute ($\partial_s \partial_t f = \partial_t \partial_s f$):
$$\Delta f = \partial_s^2 f + \partial_t^2 f = - (DJ(f) \cdot \partial_s f) \partial_t f + (DJ(f) \cdot \partial_t f) \partial_s f.$$
**Crucial Fact**: The second derivatives cancel completely! The tension field $\Delta f$ contains **only first derivatives** of $f$:
$$\|\Delta f\| \le 2 \|DJ(f)\| |df|^2.$$

#### Step 2: Second Fréchet Derivative / Laplacian of the Dirichlet Energy Density
The Euclidean Dirichlet energy density is $e = \frac{1}{2} \sum_{i,j} g_{ij}(f) (\partial_s f^i \partial_s f^j + \partial_t f^i \partial_t f^j)$.
Computing $\Delta e = (\partial_s^2 + \partial_t^2) e$:
$$\Delta e = \sum g_{ij} (\partial_s^2 f^i \partial_s^2 f^j + 2 \partial_s \partial_t f^i \partial_s \partial_t f^j + \partial_t^2 f^i \partial_t^2 f^j) + \sum g_{ij} (\partial_s (\Delta f^i) \partial_s f^j + \partial_t (\Delta f^i) \partial_t f^j) + \mathcal{Q}(Dg, D^2g, df).$$

The first term is the squared norm of the Hessian:
$$\|D^2 f\|_g^2 = \sum g_{ij} (\partial_s^2 f^i \partial_s^2 f^j + 2 \partial_s \partial_t f^i \partial_s \partial_t f^j + \partial_t^2 f^i \partial_t^2 f^j) \ge 0.$$

#### Step 3: Differentiating the Tension Field and Young's Inequality Absorption
Substitute $\Delta f$ from Step 1 into $\langle \nabla \Delta f, df \rangle_g$:
$$\partial_s (\Delta f) = - (D^2J(f)(\partial_s f, \partial_s f)) \partial_t f - (DJ(f) \cdot \partial_s^2 f) \partial_t f - (DJ(f) \cdot \partial_s f) \partial_s \partial_t f + \dots$$
Contracting with $df$ gives terms of two types:
1. **Quartic first-derivative terms**: $D^2 J * (df)^{\otimes 4}$, bounded by $\|D^2 J\| |df|^4$.
2. **Cubic terms involving $D^2 f$**: $DJ * D^2 f * (df)^{\otimes 2}$.
By Young's inequality ($a b \le \varepsilon a^2 + \frac{1}{4\varepsilon} b^2$ with $\varepsilon = 1/2$):
$$| \langle DJ * D^2 f * df, df \rangle | \le \frac{1}{2} \|D^2 f\|^2 + C_1 \|DJ\|^2 |df|^4.$$
The $\frac{1}{2} \|D^2 f\|^2$ is **absorbed** into the positive Hessian term $\|D^2 f\|_g^2$!

#### Step 4: Compactness Bounds and Quadratic Differential Inequality
Since $M$ is compact, $\sup_{x \in M} \|DJ(x)\| \le K_1$ and $\sup_{x \in M} \|D^2 J(x)\| \le K_2$.
Similarly, the Riemannian metric derivatives are uniformly bounded by $\sup \|Dg\| \le K_3$ and $\sup \|D^2 g\| \le K_4$.
Therefore, after absorption:
$$\Delta e \ge \frac{1}{2} \|D^2 f\|^2 - b e^2 \ge - b e^2,$$
where $b = 4(C_1 K_1^2 + K_2 + K_3^2 + K_4)$.
On a flat domain, $c = 0$. On a curved domain or under stereographic pullback of the spherical metric, a lower-order term $c e$ arises from the scalar curvature of the domain, giving:
$$\Delta e \ge - b e^2 - c e.$$

---

## 5. Model A Decomposition: Concrete Sub-Lemmas for Gemma 9B Prover

To bridge Contract A02 to zero `sorryAx`, we decompose `bochner_curvature_term_bound` and `contDiff_energy_density_chart` into 8 fine-grained, self-contained sub-lemmas.

### Sub-Lemma 1: Smoothness of Composition with Stereographic Projection
```lean
/-- The inverse stereographic chart from ℂ into CP1 is smooth (ContMDiff ∞). -/
lemma contMDiff_stereo_chart_symm :
    ContMDiff 𝓘(ℝ, ℂ) I_CP1 ∞ stereo_chart.symm
```
- **Difficulty**: S (Direct consequence of Mathlib's smoothness of stereographic projection).
- **Target Prover**: Local Gemma 9B with `exact?` / `apply ContMDiff.comp`.

### Sub-Lemma 2: Smoothness of Chart Pullback Map
```lean
/-- If u : CP1 → M is J-holomorphic, then u ∘ stereo_chart.symm is smooth on ℂ. -/
lemma contMDiff_u_stereo_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ContMDiff 𝓘(ℝ, ℂ) I ∞ (u ∘ stereo_chart.symm)
```
- **Difficulty**: S (`hu.1.comp contMDiff_stereo_chart_symm`).
- **Target Prover**: Local Gemma 9B.

### Sub-Lemma 3: Smoothness of Chart Energy Density (`contDiff_energy_density_chart`)
```lean
/-- Full resolution of the sorry at Bochner.lean:154:
Smoothness of the stereographic chart Riemannian energy density. -/
lemma contDiff_energy_density_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M]
    (u : CP1 → M) (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    ContDiff ℝ ∞ (fun w : ℂ => riemannianEnergyDensity I u (stereo_chart.symm w))
```
- **Difficulty**: M (Contraction of smooth differential `mfderiv` with smooth metric tensor $g$).
- **Target Prover**: Combination of `contMDiff_u_stereo_symm` and `ContDiff.mul` / `ContDiff.add`.

### Sub-Lemma 4: Cauchy-Riemann Commutation and Tension Field Identity
```lean
/-- In any local coordinate chart, the Laplacian of a J-holomorphic curve u
equals a quadratic contraction of the differential with DJ(u). -/
lemma laplacian2D_cauchy_riemann_tension_bound
    (f : ℂ → EuclideanSpace ℝ (Fin (2 * n)))
    (J_mat : EuclideanSpace ℝ (Fin (2 * n)) → (EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n))))
    (h_cr : ∀ z, fderiv ℝ f z (c_equiv_e2 Complex.I) = J_mat (f z) (fderiv ℝ f z (c_equiv_e2 1)))
    (K_DJ : ℝ) (h_DJ : ∀ x, ‖fderiv ℝ J_mat x‖ ≤ K_DJ) (w : ℂ) :
    ‖laplacian2D f w‖ ≤ 2 * K_DJ * ‖fderiv ℝ f w‖^2
```
- **Difficulty**: M (Schwarz mixed-partial cancellation $\partial_s \partial_t f = \partial_t \partial_s f$).
- **Target Prover**: Local Gemma 9B with `ext`, `ring`, `norm_mul`.

### Sub-Lemma 5: Scalar Young's Inequality Absorption
```lean
/-- Elementary algebraic lemma: Absorption of second derivatives in Bochner inequality. -/
lemma young_absorption_bochner (H D K : ℝ) (hD : 0 ≤ D) :
    - (H * D * K) ≤ (1 / 2 : ℝ) * H^2 + (1 / 2 : ℝ) * K^2 * D^2
```
- **Difficulty**: S.
- **Proof**: `have := sq_nonneg (H - K * D); linarith`.
- **Target Prover**: Local Gemma 9B (Pure elementary algebra).

### Sub-Lemma 6: Algebraic Weitzenböck Decomposition from Lower Bound
```lean
/-- Pure algebraic equivalence: A lower bound L ≥ -B with B ≥ 0 yields an exact
Weitzenböck decomposition L = H² + K with |K| ≤ B. -/
lemma weitzenboeck_decomposition_of_lower_bound (L B : ℝ) (hB : 0 ≤ B) (hL : -B ≤ L) :
    ∃ (H K : ℝ), L = H^2 + K ∧ |K| ≤ B
```
- **Difficulty**: S.
- **Proof**:
  Take `K := -B`, `H := Real.sqrt (L + B)`.
  Then `0 ≤ L + B`, so `H^2 = L + B`.
  `H^2 + K = L + B - B = L`, and `|K| = |-B| = B ≤ B`.
- **Target Prover**: Local Gemma 9B (Zero external dependencies).

### Sub-Lemma 7: Uniform Target Bounds from Compactness
```lean
/-- On a compact tame symplectic manifold, the C² norms of J and g are uniformly bounded. -/
lemma closed_tame_target_uniform_geometry_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [tgt : ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (x : M) (v w : TangentSpace I x),
        ‖tgt.J x‖ ≤ b ∧ ‖ClosedTameTarget.metric I x v w‖ ≤ c * ‖v‖ * ‖w‖
```
- **Difficulty**: M (Compactness of $M$ via `isCompact_univ.exists_isMaxOn`).
- **Target Prover**: Mathlib compactness lemmas (`Continuous.exists_forall_le`).

### Sub-Lemma 8: Resolution of `bochner_curvature_term_bound`
```lean
/-- Full resolution of the sorry at Bochner.lean:176:
Existence of uniform b, c ≥ 0 producing the Weitzenböck curvature decomposition. -/
theorem bochner_curvature_term_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompactSpace M] [ClosedTameTarget I M] :
    ∃ (b c : ℝ), 0 ≤ b ∧ 0 ≤ c ∧
      ∀ (u : CP1 → M),
        JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ →
        ∀ (w : ℂ),
          ∃ (hessNorm : ℝ) (curvTerm : ℝ),
            laplacian2D (fun z => riemannianEnergyDensity I u (stereo_chart.symm z)) w =
              hessNorm ^ 2 + curvTerm ∧
            |curvTerm| ≤
              b * (riemannianEnergyDensity I u (stereo_chart.symm w)) ^ 2 +
              c * (riemannianEnergyDensity I u (stereo_chart.symm w))
```
- **Difficulty**: M.
- **Proof Strategy**: Combine Sub-Lemmas 4, 5, 7 to establish the lower bound $\Delta_w e \ge -b e^2 - c e$, then apply Sub-Lemma 6 (`weitzenboeck_decomposition_of_lower_bound`) with $B = b e^2 + c e \ge 0$.

---

## 6. Downstream Interface Wiring & Verification

### 6.1 Wiring to `epsilon_regularity` (`A03`)
In `GromovCompactness/Analysis/EpsilonRegularity.lean`:
```lean
theorem epsilon_regularity ... :
  obtain ⟨b, c, hb, hc, h_boch⟩ := bochner_differential_inequality (M := M) I
  obtain ⟨η, C, hη, hC, h_smv⟩ := scalar_mean_value_inequality b hb c hc
  ...
```
Once `bochner_differential_inequality` is closed with 0 `sorryAx`, `h_boch` is completely discharged without axioms beyond `[propext, Classical.choice, Quot.sound]`.

### 6.2 Wiring to `TargetThresholds` (`B01`)
In `GromovCompactness/Analysis/HoferRescaling.lean`:
```lean
theorem exists_target_thresholds : Nonempty (TargetThresholds I M) := by
  obtain ⟨ε_reg, C_reg, hε_reg, hC_reg, h_reg⟩ := epsilon_regularity (M := M) I
  obtain ⟨ε_sph, hε_sph, h_sph⟩ := sphere_energy_gap (M := M) I
  obtain ⟨C_neck, a_decay, ε_neck, hC_neck, ha_decay, hε_neck, h_neck⟩ :=
    cylinder_exponential_decay (M := M) I
  exact exists_target_thresholds_of_modules I ...
```
`TargetThresholds` is the central gateway consumed by `resolve_single_defect_tree` (B07), `assemble_prestable_limit` (G01), and `gromov_compactness_genus_zero`.

### 6.3 Kernel Axiom Census Gate Check
Verification that Contract A02 is 100% compliant with the §0 directive:
- Build command: `lake build GromovCompactness.Analysis.Bochner`
- Axiom Census command: `MODULE_PREFIX=GromovCompactness.Analysis lake env lean tests/PhaseAxiomCensus.lean`
- Requirement: Zero `sorryAx` among `GromovCompactness.Analysis` declarations.
