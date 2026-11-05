# Handoff Report: Task P0-2 Unconditional Energy Conformal Invariance

- **Agent**: `explorer_m2_2`
- **Working Directory**: `/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/explorer_m2_2`
- **Target File**: `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Analysis/Energy.lean`
- **Task**: P0-2 Unconditional Conformal Invariance of Symplectic Energy
- **Status**: Investigation Complete

---

## 1. Observation

### 1.1 The Circular Hypothesis in `Energy.lean`
In `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Analysis/Energy.lean`, lines 304–310 state:
```lean
/-- Conformal invariance of the symplectic energy measure:
For any Möbius frame $\phi \in \operatorname{PSL}(2, \mathbb{C})$ and measurable set $A \subseteq \mathbb{CP}^1$,
when the energy measure pulls back equivariantly under the conformal diffeomorphism $\phi$,
$$E(u \circ \phi; \phi^{-1}(A)) = E(u; A).$$ -/
theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1)
    (h_conf : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)) :
    energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A := by
  dsimp [energyMeasure]
  rw [h_conf]
  rw [moebius_map_preimage_all (energyMeasureExtended I u) ϕ A]
```
Where `moebius_map_preimage_all` (lines 289–298) is simply:
```lean
theorem moebius_map_preimage_all (μ : Measure CP1) (ϕ : MoebiusFrame) (A : Set CP1) :
    (Measure.map ϕ.toHomeo.symm μ) (ϕ.toHomeo ⁻¹' A) = μ A := by
  let e := ϕ.toHomeo.symm.toMeasurableEquiv
  have he : ⇑e = ⇑ϕ.toHomeo.symm := rfl
  rw [← he, e.map_apply]
  have h_eq : (⇑e ⁻¹' (ϕ.toHomeo ⁻¹' A)) = A := by
    change ϕ.toHomeo.symm ⁻¹' (ϕ.toHomeo ⁻¹' A) = A
    ext x
    simp
  rw [h_eq]
```
And `energyMeasure` is defined at line 212 as:
```lean
noncomputable def energyMeasure (u : CP1 → M) (A : Set CP1) : ℝ :=
  (energyMeasureExtended I u A).toReal
```

### 1.2 Specification in `COMPLETION_PLAN.md` and `ORIGINAL_REQUEST.md`
- `COMPLETION_PLAN.md`, line 54:
  > `| **P0-2** | Critical | energy_conformal_invariant takes the invariance itself (h_conf) as a hypothesis. | Prove Möbius invariance of the repaired energy measure unconditionally (affine maps via change of variables on ℂ; inversion via the second chart, or intrinsically via isometry/conformality on S²). | Theorem without h_conf, sorry-free. |`
- `ORIGINAL_REQUEST.md`, lines 255–256:
  > `Start with P0-1 & P0-2 (GromovCompactness/Analysis/Energy.lean): Fix the energy measure definition so it includes the stereographic spherical area Jacobian (2/(1+|w|^2))^2 (or intrinsic spherical measure on CP1), prove energyMeasureExtended u Set.univ < ⊤ for smooth maps before calling .toReal, prove a concrete non-constant smooth map has finite positive energy, and prove energy_conformal_invariant without the circular h_conf hypothesis.`
- `GROMOV_COMPACTNESS_BLUEPRINT.md`, lines 443–444:
  ```lean
  theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) :
      energyMeasure I M (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I M u A := by sorry
  ```
  The original blueprint never had `h_conf`.

### 1.3 Available Structures in `Sphere.lean`
In `/Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Geometry/Sphere.lean`:
- `CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` (line 42).
- `stereo_chart : PartialHomeomorph CP1 ℂ` (line 98).
- `stereo_chart.source = {north_pole}ᶜ` (line 101) and `stereo_chart.target = Set.univ` (line 105).
- `MoebiusFrame` structure (lines 1109–1117):
  ```lean
  structure MoebiusFrame where
    matrix : MoebiusMatrix
    toHomeo : CP1 ≃ₜ CP1
    is_smooth : ContMDiff I_CP1 I_CP1 ∞ toHomeo
    is_smooth_symm : ContMDiff I_CP1 I_CP1 ∞ toHomeo.symm
  ```
- Constructors / Generators:
  - `MoebiusFrame.id` (line 1124)
  - `MoebiusFrame.comp` (line 1131)
  - `MoebiusFrame.inv` (line 1138)
  - `affine_scaling (a : ℂ) (scale : ℝ) (hscale : 0 < scale) : MoebiusFrame` (line 1288) with `toHomeo := dil_homeo scale hscale`
  - `rotation (θ : ℝ) : MoebiusFrame` (line 1268) with `toHomeo := rot_homeo θ`
  - `inversion : MoebiusFrame` (line 1249) with `toHomeo := inv_homeo`

### 1.4 Downstream Usage
Grep search across all modules in `GromovCompactness/` reveals that `energy_conformal_invariant` is currently referenced **only** in `Energy.lean` (definition and `#print axioms`). No other module in the repository has called it yet, meaning its signature can be cleaned up without causing cascading build errors in downstream files.

---

## 2. Logic Chain

### Step 1: Anatomizing the Circularity of `h_conf`
From Observation 1.1:
1. `energy_conformal_invariant` takes as hypothesis:
   `h_conf : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)`.
2. The conclusion is:
   `energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A`.
3. Because `energyMeasure I u A := (energyMeasureExtended I u A).toReal`, evaluating `h_conf` on the set `ϕ.toHomeo ⁻¹' A` yields:
   `(energyMeasureExtended I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A)).toReal = ((Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)) (ϕ.toHomeo ⁻¹' A)).toReal`.
4. By definition of pushforward measure, `(Measure.map f μ) (f ⁻¹' A) = μ A`.
5. Therefore, the proof reduces to a tautological rewrite: it assumes the measure-level conformal invariance to prove the set-level conformal invariance. The analytical substance (derivative transformation vs. area transformation) was completely omitted.

### Step 2: The Two-Dimensional Conformal Cancellation Mechanism
Let $(M, g)$ be a Riemannian manifold, $u : \Sigma \to M$ a map, and $\phi : \Sigma \to \Sigma$ a conformal map with conformal factor $\lambda(z) > 0$, so that $\phi^* g_\Sigma = \lambda^2 g_\Sigma$.
In dimension $\dim_\mathbb{R} \Sigma = 2$:
1. **Tangent vector transformation**: For an orthonormal basis $(e_1, e_2)$ of $T_z \Sigma$, the vectors $d\phi(z) e_1$ and $d\phi(z) e_2$ are orthogonal and have norm $\|d\phi(z) e_i\| = \lambda(z)$.
2. **Derivative norm transformation**:
   $$\|d(u \circ \phi)(z)\|^2_{g_\Sigma} = \|du(\phi(z)) \circ d\phi(z)\|^2_{g_\Sigma} = \lambda(z)^2 \|du(\phi(z))\|^2_{g_\Sigma}.$$
   More specifically, in local coordinates where $L = d\phi(z)$ is $\mathbb{C}$-linear ($L \circ J = J \circ L$):
   $$\|T(L e_1)\|^2 + \|T(L e_2)\|^2 = \det(L) \cdot (\|T e_1\|^2 + \|T e_2\|^2),$$
   where $\det(L) = \lambda(z)^2$. This algebraic identity holds for any linear map $T : \mathbb{R}^2 \to T_{u(z)} M$ and any symmetric bilinear form on $T M$, without assuming $u$ is $J$-holomorphic.
3. **Volume form transformation**:
   $$\phi^* (d\mathrm{vol}_\Sigma) = \det(d\phi(z)) \, d\mathrm{vol}_\Sigma = \lambda(z)^2 \, d\mathrm{vol}_\Sigma.$$
4. **Energy 2-form invariance**:
   The energy measure integrand is $\frac{1}{2} \|d(u \circ \phi)\|^2 d\mathrm{vol}_\Sigma$.
   Under pullback by $\phi$:
   $$\phi^* \left( \frac{1}{2} \|du\|^2 d\mathrm{vol}_\Sigma \right) = \left( \frac{1}{2} \|du(\phi(z))\|^2 \right) \cdot \phi^* (d\mathrm{vol}_\Sigma) = \frac{1}{2} \|du(\phi(z))\|^2 \lambda(z)^2 d\mathrm{vol}_\Sigma = \frac{1}{2} \|d(u \circ \phi)(z)\|^2 d\mathrm{vol}_\Sigma.$$
   Hence:
   $$\int_{\phi^{-1}(A)} \frac{1}{2} \|d(u \circ \phi)\|^2 d\mathrm{vol}_\Sigma = \int_A \frac{1}{2} \|du\|^2 d\mathrm{vol}_\Sigma.$$

### Step 3: Coordinate Cancellation on $\mathbb{C}$ via Stereographic Projection
Under stereographic projection $\sigma : S^2 \setminus \{\infty\} \to \mathbb{C}$:
1. Let $\rho(w) = \frac{2}{1 + |w|^2}$ (or $\frac{4}{4 + |w|^2}$ in Mathlib's metric convention).
2. The round metric on $S^2$ pulls back to $g_{S^2} = \rho(w)^2 (dx^2 + dy^2)$.
3. The derivative norm satisfies $\|du\|^2_{g_{S^2}} = \rho(w)^{-2} \|\nabla (u \circ \sigma^{-1})\|^2_{\text{Euc}}$.
4. The area element is $d\mathrm{vol}_{S^2} = \rho(w)^2 dx dy$.
5. When multiplied:
   $$\frac{1}{2} \|du\|^2_{g_{S^2}} d\mathrm{vol}_{S^2} = \frac{1}{2} \|\nabla (u \circ \sigma^{-1})\|^2_{\text{Euc}} dx dy.$$
   The stereographic factor $\rho(w)^2$ **cancels identically** with $\rho(w)^{-2}$.
6. For any holomorphic map $\psi : \mathbb{C} \to \mathbb{C}$ (e.g. $\psi(z) = a + \lambda z$ or $1/z$):
   $$\|\nabla (v \circ \psi)(z)\|^2_{\text{Euc}} = |\psi'(z)|^2 \|\nabla v(\psi(z))\|^2_{\text{Euc}}.$$
   And the Lebesgue Jacobian determinant is $\operatorname{Jac}_\mathbb{R}(\psi)(z) = |\psi'(z)|^2$.
   By Mathlib's change of variables theorem (`lintegral_image_eq_lintegral_abs_det_fderiv_mul` or `map_addHaar_smul`), the factor $|\psi'(z)|^2$ cancels with the volume expansion.

### Step 4: Verification of `Sphere.lean` Generators
From Observation 1.3:
1. `dil_homeo l hl`: On $\mathbb{R}^3$, $(x_0, x_1, x_2) \mapsto (2 l x_0 / D, 2 l x_1 / D, ((1 - l^2) + (1 + l^2) x_2) / D)$.
   In stereographic coordinates $w = \sigma(x) = \frac{x_0 + i x_1}{1 - x_2}$:
   $$1 - x_2' = \frac{2 l^2 (1 - x_2)}{D}, \quad x_0' + i x_1' = \frac{2 l (x_0 + i x_1)}{D}.$$
   Therefore $\sigma(x') = \frac{x_0' + i x_1'}{1 - x_2'} = l^{-1} \sigma(x)$.
   This is strictly linear scaling on $\mathbb{C}$!
2. `rot_homeo θ`: Rotates $(x_0, x_1)$ by $\theta$ while fixing $x_2$.
   In stereographic coordinates, $\sigma(x') = e^{i\theta} \sigma(x)$.
   This is strictly rotation on $\mathbb{C}$!
3. `inv_homeo`: Maps $(x_0, x_1, x_2) \mapsto (x_0, -x_1, -x_2)$.
   In stereographic coordinates:
   $$\frac{x_0 - i x_1}{1 + x_2} = \frac{(x_0 - i x_1)(1 - x_2)}{x_0^2 + x_1^2} = \frac{1 - x_2}{x_0 + i x_1} = \frac{1}{\sigma(x)}.$$
   This is strictly conformal inversion $w \mapsto 1/w$ on $\mathbb{C}^*$!
4. Singular points $\{0, \infty\}$: In `Energy.lean`, `energy_point_null` (line 261) proves that any single point has energy measure zero:
   `energyMeasure I u {p} = 0`.
   Thus excise of $\{\infty\}$ and $\{0\}$ does not alter the energy measure.

---

## 3. Caveats

1. **Coupling with Task P0-1**:
   In `COMPLETION_PLAN.md`, P0-1 identifies that the existing `energyMeasureExtended` integrates `riemannianEnergyDensity` against flat Lebesgue measure on $\mathbb{C}$ without the Jacobian $\rho(w)^2$, which causes $E(u) = \infty$ for generic smooth maps.
   P0-2 must be implemented on the **repaired** energy measure from P0-1 (either chartwise Euclidean or intrinsic spherical). The conformal cancellation $\lambda^2 \cdot \lambda^{-2} = 1$ derived here applies equally to both repairs.
2. **Smoothness / Differentiability Scope**:
   In Mathlib, `mfderiv` returns `0` if a map is not differentiable at a point. If $u$ is smooth ($C^1$ or $C^\infty$), the chain rule `mfderiv_comp` holds pointwise everywhere. For the unconditional theorem, stating the result for smooth maps `ContMDiff I_CP1 I ∞ u` (or for all maps where `u ∘ ϕ` and $u$ are differentiable almost everywhere) avoids measure-theoretic non-measurability pitfalls.
3. **Möbius Frame Extensionality**:
   `MoebiusFrame` currently consists of a matrix and a homeomorphism with smoothness proofs. In `Sphere.lean`, every concrete instance (`affine_scaling`, `rotation`, `inversion`) is conformal. For the general case of arbitrary `ϕ : MoebiusFrame`, the proof can proceed either:
   - (A) For all frames generated by the constructors (`id`, `affine_scaling`, `rotation`, `inversion`, `comp`), or
   - (B) By adding a conformality lemma or field asserting that $\phi$ preserves the complex structure $J_{\mathbb{CP}^1}$ on $T\mathbb{CP}^1$ (which is automatically true for all elements of $\operatorname{PSL}(2, \mathbb{C})$).

---

## 4. Conclusion

The circular hypothesis `h_conf` in `energy_conformal_invariant` can and must be completely removed.

### 4.1 Unconditional Theorem Statement
```lean
/-- Conformal invariance of the symplectic energy measure:
For any Möbius transformation frame $\phi \in \operatorname{PSL}(2, \mathbb{C})$ and measurable set $A \subseteq \mathbb{CP}^1$,
$$E(u \circ \phi; \phi^{-1}(A)) = E(u; A).$$ -/
theorem energy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) (A : Set CP1) :
    energyMeasure I (u ∘ ϕ.toHomeo) (ϕ.toHomeo ⁻¹' A) = energyMeasure I u A

/-- Conformal invariance of total energy $E(u \circ \phi) = E(u)$. -/
theorem totalEnergy_conformal_invariant (u : CP1 → M) (ϕ : MoebiusFrame) :
    totalEnergy I (u ∘ ϕ.toHomeo) = totalEnergy I u
```

### 4.2 Intermediate Lemma Decomposition for the Implementer

The implementer should structure the proof across 6 modular lemmas:

1. **`metric_c_linear_trace_scaling`** (Pointwise 2D algebraic cancellation):
   For any symmetric bilinear form $g$ on $V$, any linear map $T : \mathbb{R}^2 \to V$, and any $\mathbb{C}$-linear map $L : \mathbb{R}^2 \to \mathbb{R}^2$ with $L = \begin{pmatrix} a & -b \\ b & a \end{pmatrix}$:
   $$g(T(L e_1), T(L e_1)) + g(T(L e_2), T(L e_2)) = (a^2 + b^2) (g(T e_1, T e_1) + g(T e_2, T e_2)).$$
   *Proof*: Direct expansion via bilinearity (`ring`).

2. **`energyMeasureExtended_rotation_invariant`** (Rotation invariance):
   For any $\theta \in \mathbb{R}$:
   $$\mathrm{energyMeasureExtended} \; I (u \circ (\mathrm{rotation} \; \theta).\mathrm{toHomeo}) = \mathrm{Measure.map} \; (\mathrm{rotation} \; \theta).\mathrm{toHomeo.symm} \; (\mathrm{energyMeasureExtended} \; I u).$$
   *Proof*: Rotation is a linear isometry of $\mathbb{C}$, preserving both Dirichlet norm and Lebesgue measure.

3. **`energyMeasureExtended_scaling_invariant`** (Dilation invariance):
   For any $a \in \mathbb{C}$, $\lambda > 0$:
   $$\mathrm{energyMeasureExtended} \; I (u \circ (\mathrm{affine\_scaling} \; a \; \lambda \; h\lambda).\mathrm{toHomeo}) = \mathrm{Measure.map} \; (\mathrm{affine\_scaling} \; a \; \lambda \; h\lambda).\mathrm{toHomeo.symm} \; (\mathrm{energyMeasureExtended} \; I u).$$
   *Proof*: Derivative scales by $\lambda$, energy density scales by $\lambda^2$; Lebesgue measure scales by $\lambda^{-2}$ via `map_addHaar_smul`. They cancel identically.

4. **`energyMeasureExtended_inversion_invariant`** (Inversion invariance):
   $$\mathrm{energyMeasureExtended} \; I (u \circ \mathrm{inversion.toHomeo}) = \mathrm{Measure.map} \; \mathrm{inversion.toHomeo.symm} \; (\mathrm{energyMeasureExtended} \; I u).$$
   *Proof*: On $\mathbb{C}^*$, $w \mapsto 1/w$ has derivative norm $1/|w|^2$ and real Jacobian $1/|w|^4$. Derivative squared scales by $1/|w|^4$, which cancels the Jacobian via `Mathlib.MeasureTheory.Function.Jacobian.lintegral_image_eq_lintegral_abs_det_fderiv_mul`. Points $\{0, \infty\}$ have measure zero by `energy_point_null`.

5. **`energyMeasureExtended_comp`** (Composition functoriality):
   If invariance holds for $\phi_1$ and $\phi_2$, then:
   $$\mathrm{energyMeasureExtended} \; I (u \circ (\phi_1 \circ \phi_2)) = \mathrm{Measure.map} \; (\phi_1 \circ \phi_2).\mathrm{symm} \; (\mathrm{energyMeasureExtended} \; I u).$$
   *Proof*: `Measure.map_map` in Mathlib.

6. **`energyMeasureExtended_conformal_invariant`** (Main Equivariance):
   Unconditional proof that `energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)` for any Möbius frame $\phi$.
   Then `energy_conformal_invariant` applies `moebius_map_preimage_all` in 2 lines with **zero hypotheses**.

---

## 5. Verification Method

To verify the completion of Task P0-2:

1. **Grep Check**:
   Confirm that the hypothesis `h_conf` is absent from `GromovCompactness/Analysis/Energy.lean`:
   ```bash
   grep -n "h_conf" /Users/pablosuarez/Desktop/SympTopAutoForm/GromovCompactness/Analysis/Energy.lean
   ```
   *Expected output*: 0 matches.

2. **Compilation and Axiom Census**:
   ```bash
   lake build GromovCompactness
   ```
   Check that `energy_conformal_invariant` depends only on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`):
   ```lean
   #print axioms GromovCompactness.energy_conformal_invariant
   ```
   *Invalidation Condition*: If `#print axioms` outputs `sorryAx`, or if compilation fails with type errors, the task is incomplete.
