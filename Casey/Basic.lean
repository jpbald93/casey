/-
Copyright (c) 2026. All rights reserved.

# Casey's theorem: basic definitions and the tangent-length lemma

We work in an arbitrary real inner product space `V` with a Euclidean affine space `P`
(so in particular `EuclideanSpace ℝ (Fin 2)`).

A circle `Γ` has centre `O` and radius `R > 0`. A circle of radius `r` that is internally
tangent to `Γ` at a point `T ∈ Γ` has centre `O + (1 - r / R) • (T - O)`; this is
`Casey.tangentCentre O T R r`. (If `r < 0`, the same formula describes the circle of radius
`|r|` *externally* tangent to `Γ` at `T`; the results below only need `r ≤ R`.)

The length of the common tangent of two circles with centres `c₁ c₂` and (signed) radii
`r₁ r₂` is `√(dist c₁ c₂ ^ 2 - (r₁ - r₂) ^ 2)`; this is `Casey.tangentLength`.
-/
import Mathlib.Geometry.Euclidean.Sphere.Ptolemy

namespace Casey

open EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- The centre of the circle of radius `r` internally tangent at `T` to the circle with
centre `O` and radius `R`. -/
noncomputable def tangentCentre (O T : P) (R r : ℝ) : P :=
  ((1 - r / R) • (T -ᵥ O)) +ᵥ O

/-- The length of the common (external) tangent of the circles with centres `c₁`, `c₂` and
radii `r₁`, `r₂`: `√(d² - (r₁ - r₂)²)`. -/
noncomputable def tangentLength (c₁ c₂ : P) (r₁ r₂ : ℝ) : ℝ :=
  Real.sqrt (dist c₁ c₂ ^ 2 - (r₁ - r₂) ^ 2)

theorem tangentLength_comm (c₁ c₂ : P) (r₁ r₂ : ℝ) :
    tangentLength c₁ c₂ r₁ r₂ = tangentLength c₂ c₁ r₂ r₁ := by
  unfold tangentLength
  rw [dist_comm c₁ c₂]
  ring_nf

/-- A circle of radius `0` tangent at `T` is the point `T` itself. -/
theorem tangentCentre_zero (O T : P) (R : ℝ) : tangentCentre O T R 0 = T := by
  simp [tangentCentre]

/-- The tangent length between two point-circles is their distance. -/
theorem tangentLength_zero (c₁ c₂ : P) : tangentLength c₁ c₂ 0 0 = dist c₁ c₂ := by
  simp [tangentLength, Real.sqrt_sq dist_nonneg]

/-- The centre `tangentCentre O T R r` is at distance `|R - r|` from `O`. -/
theorem dist_tangentCentre_center {O T : P} {R : ℝ} (r : ℝ) (hR : R ≠ 0)
    (hT : dist T O = R) : dist (tangentCentre O T R r) O = |R - r| := by
  unfold tangentCentre
  rw [dist_eq_norm_vsub V, vadd_vsub, norm_smul, ← dist_eq_norm_vsub V, hT,
    Real.norm_eq_abs]
  have : R - r = (1 - r / R) * R := by field_simp
  rw [this, abs_mul, ← hT, abs_of_nonneg dist_nonneg]

/-- **Key lemma** (pure algebra): for two circles internally tangent to `Γ(O, R)` at
`T₁`, `T₂`,
`d(c₁, c₂)² - (r₁ - r₂)² = |T₁T₂|² (R - r₁)(R - r₂) / R²`. -/
theorem dist_tangentCentre_sq_sub_sq {O T₁ T₂ : P} {R : ℝ} (r₁ r₂ : ℝ) (hR : R ≠ 0)
    (h₁ : dist T₁ O = R) (h₂ : dist T₂ O = R) :
    dist (tangentCentre O T₁ R r₁) (tangentCentre O T₂ R r₂) ^ 2 - (r₁ - r₂) ^ 2 =
      dist T₁ T₂ ^ 2 * ((R - r₁) * (R - r₂)) / R ^ 2 := by
  unfold tangentCentre
  rw [dist_eq_norm_vsub V, vadd_vsub_vadd_cancel_right, dist_eq_norm_vsub V T₁ T₂,
    ← vsub_sub_vsub_cancel_right T₁ T₂ O]
  rw [dist_eq_norm_vsub V] at h₁ h₂
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, h₁, h₂, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
    sq_abs, sq_abs]
  field_simp
  ring

/-- **Tangent-length formula**: `t₁₂ = |T₁T₂| √(R - r₁) √(R - r₂) / R`. -/
theorem tangentLength_tangentCentre {O T₁ T₂ : P} {R r₁ r₂ : ℝ} (hR : 0 < R)
    (hr₁ : r₁ ≤ R) (hr₂ : r₂ ≤ R) (h₁ : dist T₁ O = R) (h₂ : dist T₂ O = R) :
    tangentLength (tangentCentre O T₁ R r₁) (tangentCentre O T₂ R r₂) r₁ r₂ =
      dist T₁ T₂ * (Real.sqrt (R - r₁) * Real.sqrt (R - r₂)) / R := by
  have ha : 0 ≤ R - r₁ := sub_nonneg.2 hr₁
  have hb : 0 ≤ R - r₂ := sub_nonneg.2 hr₂
  unfold tangentLength
  rw [dist_tangentCentre_sq_sub_sq r₁ r₂ hR.ne' h₁ h₂]
  have : dist T₁ T₂ ^ 2 * ((R - r₁) * (R - r₂)) / R ^ 2 =
      (dist T₁ T₂ * (Real.sqrt (R - r₁) * Real.sqrt (R - r₂)) / R) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]
  rw [this, Real.sqrt_sq (by positivity)]

end Casey
