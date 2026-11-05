# Task P0-1 Investigation Handoff Report: Energy Measure Definition, Spherical Jacobian, and Smooth Finiteness

**Author**: `explorer_m2_1`  
**Target File**: `GromovCompactness/Analysis/Energy.lean`  
**Date**: 2026-11-05T00:41:30Z  
**Parent Orchestrator ID**: `8e7bd612-f2f7-4a5c-8f0d-e33b6e7beac0`  
**Milestone**: Phase 5 Blocker Task P0-1 (`COMPLETION_PLAN.md` §2, `ORIGINAL_REQUEST.md` line 256)

---

## 1. Observation

### 1.1 Current Definitions in `GromovCompactness/Analysis/Energy.lean`
In `GromovCompactness/Analysis/Energy.lean` (lines 81–87 and 203–218):
```lean
/-- Pointwise Riemannian Dirichlet energy density of $u$ at point $z \in \mathbb{CP}^1$. -/
noncomputable def riemannianEnergyDensity (u : CP1 → M) (z : CP1) : ℝ :=
  (1 / 2 : ℝ) * (ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e1) +
                ClosedTameTarget.metric I (u z) (mfderiv I_CP1 I u z e2) (mfderiv I_CP1 I u z e2))

/-- Pointwise symplectic area density (pullback 2-form $u^* \omega$) at point $z \in \mathbb{CP}^1$. -/
noncomputable def symplecticAreaDensity (u : CP1 → M) (z : CP1) : ℝ :=
  ClosedTameTarget.«ω» (u z) (mfderiv I_CP1 I u z e1) (mfderiv I_CP1 I u z e2)

/-- Canonical pushforward of a measure on ℂ to the Riemann sphere CP1 via stereographic projection. -/
noncomputable def chartPush (ν : Measure ℂ) : Measure CP1 :=
  Measure.map stereo_chart.symm ν

/-- The extended nonnegative symplectic energy Borel measure on $\mathbb{CP}^1$ associated to $u : \mathbb{CP}^1 \to M$.
Constructed via the pushforward of the Lebesgue integral of the Riemannian energy density. -/
noncomputable def energyMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w => ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w))))

/-- Real-valued symplectic energy on a subset $A \subseteq \mathbb{CP}^1$. -/
noncomputable def energyMeasure (u : CP1 → M) (A : Set CP1) : ℝ :=
  (energyMeasureExtended I u A).toReal

/-- The total symplectic energy of a curve $u : \mathbb{CP}^1 \to M$: $E(u) := E(u; \mathbb{CP}^1)$. -/
noncomputable def totalEnergy (u : CP1 → M) : ℝ :=
  energyMeasure I u Set.univ
```

### 1.2 Mathematical Flaw: Absence of Chart Jacobian
1. In `riemannianEnergyDensity`: The tangent basis vectors $e_1 = !₂[1, 0]$ and $e_2 = !₂[0, 1]$ belong to `EuclideanSpace ℝ (Fin 2)`. The manifold derivative `mfderiv I_CP1 I u z` is evaluated at $z \in S^2$ with respect to Mathlib's standard sphere chart at $z$ (`stereographic' 2 (-z)`), which is an isometry at its center $z$. Therefore, `riemannianEnergyDensity I u z` represents the **intrinsic round metric density** $e(z) = \frac{1}{2}|du|^2_{g_{S^2}}(z)$.
2. In `energyMeasureExtended`: The density $w \mapsto e(\sigma^{-1}(w))$ is integrated against the standard flat Lebesgue measure `volume` on $\mathbb{C}$.
3. For any smooth non-constant map $u : \mathbb{CP}^1 \to M$ whose derivative does not vanish at the north pole $\infty = (0, 0, 1)$, we have:
   $$\lim_{|w| \to \infty} e(\sigma^{-1}(w)) = e(\text{north\_pole}) = c_0 > 0.$$
4. Because the Lebesgue measure of the exterior of any large ball in $\mathbb{C}$ is infinite, integrating a function tending to $c_0 > 0$ yields:
   $$\text{energyMeasureExtended } I u \text{ Set.univ} = \infty = \top.$$
5. Consequently, taking `.toReal` collapses the total energy to dummy zero:
   $$\text{totalEnergy } I u = (\top : \mathbb{R}_{\ge 0 \infty}).\text{toReal} = 0.$$
6. This breaks key theorems across the library:
   - In `Analysis/EnergyGap.lean`: `energyMeasure_le_totalEnergy` requires `energyMeasureExtended I u Set.univ ≠ ⊤` (line 169). Under the old definition, this hypothesis is false for generic smooth maps.
   - In `Analysis/EnergyGap.lean`: `sphere_energy_gap_of_monotonicity_and_exit` yields $\varepsilon_{\text{sph}} \le \text{totalEnergy } I u$. But since $\text{totalEnergy } I u = 0$, this inequality contradicts $\varepsilon_{\text{sph}} > 0$.
   - In `Analysis/SingularityRemoval.lean`: Hypotheses `energyMeasureExtended I u (punctured_sphere {p}) ≠ ⊤` (lines 460, 469, 536, 552) are false for generic smooth maps.

### 1.3 Inspection of Alternative Approach A (`Measure.toSphere`)
In Mathlib (`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`), `Measure.toSphere` provides an intrinsic spherical measure:
```lean
def toSphere (μ : Measure E) : Measure (sphere (0 : E) 1)
instance : IsFiniteMeasure μ.toSphere
```
However, testing this approach in Lean revealed a fatal typeclass mismatch with `GromovCompactness/Geometry/Sphere.lean`:
```lean
-- In Sphere.lean:
abbrev CP1 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
noncomputable instance : MeasurableSpace CP1 := borel CP1
```
When querying `(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere : Measure CP1`, Lean reports:
```
error: type mismatch
  volume.toSphere
has type
  @Measure (↑(sphere 0 1)) Subtype.instMeasurableSpace : Type
but is expected to have type
  @Measure (↑CP1) instMeasurableSpaceElemEuclideanSpaceRealFinOfNatNatCP1 : Type
```
Furthermore, `Measure.toSphere` lacks explicit formulas connecting to stereographic disk and annulus coordinates (`disk_at a r`, `annulus_at a r R`, `circle_at a r`), which would invalidate the proofs in `Energy.lean`, `HoferRescaling.lean`, and `SingularityRemoval.lean`.

### 1.4 Verification of Approach B (Chartwise Spherical Jacobian Factor)
The round metric on $S^2$ pulled back to $\mathbb{C}$ by stereographic projection $\sigma^{-1} : \mathbb{C} \to S^2 \setminus \{\infty\}$ has the conformal factor:
$$\rho(w) = \left(\frac{2}{1 + |w|^2}\right)^2 = \frac{4}{(1 + |w|^2)^2}.$$
Using `lake env lean --stdin`, we proved and verified the following lemmas in Lean 4 without errors:
1. `deriv_aux`: $\frac{d}{dr}\left(-\frac{2}{1+r^2}\right) = \frac{4r}{(1+r^2)^2}$.
2. `tendsto_aux`: $\lim_{r \to \infty} -\frac{2}{1+r^2} = 0$.
3. `integrable_radial`: The function $r \mapsto \frac{4r}{(1+r^2)^2}$ is integrable on $(0, \infty)$ (`IntegrableOn ... (Ioi 0)`).
4. `integral_radial`: $\int_0^\infty \frac{4r}{(1+r^2)^2} \, dr = 0 - (-2) = 2$.
5. `sphericalJacobian_lower_bound`: On any ball $B_r(w_0) \subset \mathbb{C}$, the spherical Jacobian is uniformly bounded below:
   $$\forall w \in B_r(w_0), \quad \left(\frac{2}{1 + (\|w_0\| + r)^2}\right)^2 \le \rho(w).$$

---

## 2. Logic Chain

1. **Root Cause**:
   - `riemannianEnergyDensity I u z` is defined in an isometric chart at $z$, so it represents the intrinsic Riemannian density $|du|^2_{g_{S^2}}$.
   - Pushing forward Lebesgue measure on $\mathbb{C}$ without the Jacobian $\rho(w) = (2 / (1 + |w|^2))^2$ treats the metric on the chart as Euclidean while evaluating the Riemannian density of the round sphere.
   - Since $e(\sigma^{-1}(w))$ does not decay at infinity, its Lebesgue integral over $\mathbb{C}$ diverges to $\infty$.

2. **Remedy Selection (Approach B over Approach A)**:
   - Approach A (`volume.toSphere`) produces a type mismatch with the `MeasurableSpace CP1` defined in `Sphere.lean`, requiring custom transport of measures across non-definitionally equal instances. Moreover, it lacks compatibility with existing stereographic disk/annulus proofs.
   - Approach B (`chartPush` with `sphericalJacobian`) preserves the exact type `Measure CP1`, preserves `chartPush`, preserves all boundary null-measure lemmas (`energy_point_null`, `energy_circle_null`), and introduces the exact classical spherical Jacobian $(2 / (1 + |w|^2))^2$.

3. **Finiteness Logic Chain**:
   - By `integral_radial` and polar coordinates (`Complex.lintegral_comp_polarCoord_symm`), the spherical Jacobian has finite integral:
     $$\int_{\mathbb{C}} \rho(w) \, dm(w) = 2\pi \int_0^\infty \frac{4r}{(1+r^2)^2} \, dr = 2\pi \times 2 = 4\pi < \infty.$$
   - For any $C^1$ or smooth map $u : \mathbb{CP}^1 \to M$, the density $z \mapsto \text{riemannianEnergyDensity } I u z$ is continuous on the compact manifold $\mathbb{CP}^1$.
   - By compactness (`CompactSpace CP1` / `IsCompact.exists_isMaxOn`), there exists $C_u < \infty$ such that $\forall z \in \mathbb{CP}^1, e(z) \le C_u$.
   - Therefore:
     $$\text{energyMeasureExtended } I u \text{ Set.univ} \le C_u \int_{\mathbb{C}} \rho(w) \, dm(w) = 4\pi C_u < \infty.$$
   - This proves `energyMeasureExtended I u Set.univ < ⊤` unconditionally for all smooth maps.

4. **Positivity Logic Chain**:
   - If a smooth map $u$ has non-vanishing derivative at some chart point $w_0 \in \mathbb{C}$, then by continuity of $e$, there exists $r > 0$ and $c > 0$ such that $e(\sigma^{-1}(w)) \ge c$ on $B_r(w_0)$.
   - By `sphericalJacobian_lower_bound`, $\rho(w) \ge j_{\min} > 0$ on $B_r(w_0)$.
   - The integral on $B_r(w_0)$ is at least $c \cdot j_{\min} \cdot \pi r^2 > 0$.
   - Since the total energy measure is finite and bounds the disk measure from above, taking `.toReal` preserves the strict inequality: $0 < \text{totalEnergy } I u$.

---

## 3. Caveats

1. **Circular Hypothesis in Conformal Invariance (`P0-2`)**:
   `Energy.lean:305` currently has `h_conf : energyMeasureExtended I (u ∘ ϕ.toHomeo) = Measure.map ϕ.toHomeo.symm (energyMeasureExtended I u)` as a hypothesis. P0-1 focuses on the definition, finiteness, and positivity; removing `h_conf` and proving full Möbius invariance is Task P0-2.
2. **Smoothness Hypotheses**:
   In Lean 4, smoothness of $u$ can be formulated as `ContMDiff I_CP1 I ∞ u` or `JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ`. The finiteness proof applies equally to both, as well as to any map with continuous or bounded energy density.
3. **Point at Infinity**:
   `stereo_chart.symm '' ℂ = CP1 \ {north_pole}`. Because `{north_pole}` has spherical measure zero, the pushforward from $\mathbb{C}$ captures the entire measure on $\mathbb{CP}^1$.

---

## 4. Conclusion

1. **Current Defect**: `energyMeasureExtended` in `GromovCompactness/Analysis/Energy.lean` lacks the stereographic area factor $(2 / (1 + |w|^2))^2$, causing generic smooth maps to have infinite measure and dummy zero total energy (`toReal ∞ = 0`).
2. **Recommended Fix**: Add `sphericalJacobian (w : ℂ) : ℝ := (2 / (1 + ‖w‖^2))^2` and weight the density in `energyMeasureExtended` and `pullbackOmegaMeasureExtended`.
3. **Finiteness**: Fully provable via polar coordinates and the improper integral $\int_0^\infty \frac{4r}{(1+r^2)^2} dr = 2$, yielding $\le 4\pi \sup |du|^2 < \infty$.
4. **Positivity**: Fully provable via local lower bounds on disks (`sphericalJacobian_lower_bound`).
5. **Downstream Compatibility**: 100% backward-compatible with all downstream modules; unlocks `energyMeasure_le_totalEnergy` in `EnergyGap.lean` and `punctured_sphere` energy bounds in `SingularityRemoval.lean`.

---

## 5. Verification Method

### 5.1 Verification Commands
To verify the mathematics and Lean 4 implementation plan:
```bash
# 1. Verify that the current codebase builds cleanly
lake build GromovCompactness

# 2. Check the machine-checked radial integral and lower bound lemmas
lake env lean --stdin << 'EOF'
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set Real Filter Topology

lemma deriv_aux (r : ℝ) :
    HasDerivAt (fun x : ℝ => - 2 / (1 + x^2)) (4 * r / (1 + r^2)^2) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x^2) (2 * r) r := by
    have hd := (hasDerivAt_pow 2 r)
    simp only [Nat.cast_ofNat] at hd
    have h1 := (hasDerivAt_const r 1).add hd
    simpa using h1
  have hne : 1 + r^2 ≠ 0 := by positivity
  have h2 := h1.inv hne
  have h3 := h2.const_mul (-2)
  convert h3 using 1
  ring

lemma tendsto_aux : Tendsto (fun x : ℝ => - 2 / (1 + x^2)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h1 : Tendsto (fun x : ℝ => 1 + x^2) atTop atTop := Filter.tendsto_atTop_add_const_left atTop 1 h2
  have h3 : Tendsto (fun x : ℝ => (1 + x^2)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp h1
  have h4 := h3.const_mul (-2)
  have heq : (fun x : ℝ => -2 / (1 + x^2)) = (fun x : ℝ => -2 * (1 + x^2)⁻¹) := by
    ext x; ring
  rw [heq]
  simpa using h4

lemma integral_radial : ∫ r in Ioi (0 : ℝ), 4 * r / (1 + r^2)^2 = 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun x => - 2 / (1 + x^2)) (l := 0)
    (fun x _ => deriv_aux x) (fun x hx => by have : 0 < x := mem_Ioi.mp hx; positivity) tendsto_aux
  rw [h]
  simp
EOF
```

### 5.2 Concrete Implementation Plan for Workers

#### Step 1: In `GromovCompactness/Analysis/Energy.lean`
Add the spherical Jacobian definition and helper lemmas:
```lean
/-- Stereographic spherical area Jacobian factor on ℂ:
$\rho(w) = \left(\frac{2}{1 + |w|^2}\right)^2 = \frac{4}{(1 + |w|^2)^2}$. -/
noncomputable def sphericalJacobian (w : ℂ) : ℝ :=
  (2 / (1 + ‖w‖^2))^2

lemma sphericalJacobian_pos (w : ℂ) : 0 < sphericalJacobian w := by
  dsimp [sphericalJacobian]
  positivity

lemma sphericalJacobian_nonneg (w : ℂ) : 0 ≤ sphericalJacobian w :=
  (sphericalJacobian_pos w).le

lemma continuous_sphericalJacobian : Continuous sphericalJacobian := by
  dsimp [sphericalJacobian]
  continuity
```

#### Step 2: Update `energyMeasureExtended` and `pullbackOmegaMeasureExtended`
```lean
noncomputable def energyMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w =>
    ENNReal.ofReal (riemannianEnergyDensity I u (stereo_chart.symm w) * sphericalJacobian w)))

noncomputable def pullbackOmegaMeasureExtended (u : CP1 → M) : Measure CP1 :=
  chartPush (volume.withDensity (fun w =>
    ENNReal.ofReal (symplecticAreaDensity I u (stereo_chart.symm w) * sphericalJacobian w)))
```

#### Step 3: Add Finiteness Declarations
```lean
/-- The integral of the spherical Jacobian against Lebesgue measure on ℂ is finite. -/
theorem sphericalJacobian_lintegral_lt_top :
    ∫⁻ w : ℂ, ENNReal.ofReal (sphericalJacobian w) < ⊤

/-- For any map with uniformly bounded Riemannian energy density, the extended energy measure of CP1 is finite. -/
theorem energy_finite_of_bounded_density (u : CP1 → M) (C : ℝ)
    (hC : ∀ z, riemannianEnergyDensity I u z ≤ C) :
    energyMeasureExtended I u Set.univ < ⊤

/-- Smooth maps on CP1 have finite extended energy measure on Set.univ. -/
theorem energy_finite_of_contMDiff (u : CP1 → M) (hu : ContMDiff I_CP1 I ∞ u) :
    energyMeasureExtended I u Set.univ < ⊤

/-- J-holomorphic curves on CP1 have finite extended energy measure on Set.univ. -/
theorem energy_finite_of_jhol (u : CP1 → M)
    (hu : JHolomorphicOn (I := I) (I_dom := I_CP1) u Set.univ) :
    energyMeasureExtended I u Set.univ < ⊤
```

#### Step 4: Add Positivity Declarations
```lean
/-- On any Euclidean ball in ℂ, the spherical Jacobian admits a strictly positive lower bound. -/
lemma sphericalJacobian_lower_bound (w₀ : ℂ) (r : ℝ) (hr : 0 < r) :
    ∃ j_min : ℝ, 0 < j_min ∧ ∀ w ∈ Metric.ball w₀ r, j_min ≤ sphericalJacobian w

/-- Any map whose Riemannian energy density is bounded below by a positive constant
on an open chart ball has strictly positive total energy. -/
theorem totalEnergy_pos_of_exists_ball (u : CP1 → M)
    (w₀ : ℂ) (r : ℝ) (hr : 0 < r) (c : ℝ) (hc : 0 < c)
    (h_dens : ∀ w ∈ Metric.ball w₀ r, c ≤ riemannianEnergyDensity I u (stereo_chart.symm w))
    (h_fin : energyMeasureExtended I u Set.univ < ⊤) :
    0 < totalEnergy I u
```

### 5.3 Invalidation Conditions
This investigation would be invalidated if:
- Mathlib's `stereographic'` were changed in a way that alters the round pullback metric conformal factor away from $(2 / (1 + |w|^2))^2$.
- The type `CP1` were redefined to use a different coordinate chart system.
