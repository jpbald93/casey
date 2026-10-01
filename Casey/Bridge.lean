/-
Copyright (c) 2026. All rights reserved.

# Bridge lemmas: `tangentCentre` and `tangentLength` match the classical notions

* `tangentCentre O T R r` lies on the line through `O` and `T` (the line of centres passes
  through the point of tangency);
* the circle of radius `|r|` it centres passes through `T`, with its centre at distance `|R - r|`
  from `O` (the internal/external tangency distance identities);
* `tangentLength` squares to `d² - (r₁ - r₂)²`, and for a point and a circle it is the length
  of the tangent segment whose radius is perpendicular to it.
-/
import Casey.Basic

namespace Casey

open EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- `tangentCentre O T R r` lies on the line through `O` and `T`. -/
theorem tangentCentre_mem_line (O T : P) (R r : ℝ) :
    tangentCentre O T R r ∈ line[ℝ, O, T] := by
  have : tangentCentre O T R r = AffineMap.lineMap O T (1 - r / R) := by
    simp [tangentCentre, AffineMap.lineMap_apply]
  rw [this]
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- The two centres `O`, `tangentCentre O T R r` and the tangency point `T` are collinear. -/
theorem collinear_tangentCentre (O T : P) (R r : ℝ) :
    Collinear ℝ {tangentCentre O T R r, O, T} :=
  collinear_insert_of_mem_affineSpan_pair (tangentCentre_mem_line O T R r)

/-- Tangency at `T` with signed radius: `T` is on both circles, i.e. at distance `R` from `O` and
at distance `|r|` from the centre `c = tangentCentre O T R r`, and `dist c O = |R - r|`
(`= R - r` for internal, `= R + |r|` for external tangency). -/
theorem tangentCentre_tangent {O T : P} {R : ℝ} (r : ℝ) (hR : R ≠ 0) (hT : dist T O = R) :
    dist T O = R ∧ dist T (tangentCentre O T R r) = |r| ∧
      dist (tangentCentre O T R r) O = |R - r| := by
  refine ⟨hT, ?_, dist_tangentCentre_center r hR hT⟩
  unfold tangentCentre
  rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← one_smul ℝ (T -ᵥ O), smul_smul, mul_one,
    ← sub_smul, norm_smul, ← dist_eq_norm_vsub V, hT, Real.norm_eq_abs]
  have : (1 : ℝ) - (1 - r / R) = r / R := by ring
  have h0 : 0 < R := lt_of_le_of_ne (by rw [← hT]; exact dist_nonneg) (Ne.symm hR)
  rw [this, abs_div, abs_of_pos h0, div_mul_cancel₀ _ hR]

/-- The tangent-length formula: `tangentLength c₁ c₂ r₁ r₂ ^ 2 = d² - (r₁ - r₂)²` whenever the
right-hand side is nonnegative. -/
theorem tangentLength_sq {c₁ c₂ : P} {r₁ r₂ : ℝ} (h : (r₁ - r₂) ^ 2 ≤ dist c₁ c₂ ^ 2) :
    tangentLength c₁ c₂ r₁ r₂ ^ 2 = dist c₁ c₂ ^ 2 - (r₁ - r₂) ^ 2 := by
  unfold tangentLength
  exact Real.sq_sqrt (sub_nonneg.2 h)

/-- Tangent from a point: if `X` is on the circle `(c, r)` and the radius `cX` is perpendicular
to `pX`, then `pX` is the tangent segment and its length is `tangentLength c p r 0`, i.e.
`dist p X ^ 2 = dist p c ^ 2 - r ^ 2`. -/
theorem tangentLength_eq_dist_of_perp {c p X : P} {r : ℝ} (hX : dist X c = r)
    (hperp : inner ℝ (p -ᵥ X) (X -ᵥ c) = 0) :
    tangentLength c p r 0 = dist p X ∧ dist p X ^ 2 = dist p c ^ 2 - r ^ 2 := by
  have hpy : dist p c ^ 2 = dist p X ^ 2 + r ^ 2 := by
    rw [← hX, dist_eq_norm_vsub V p c, dist_eq_norm_vsub V p X, dist_eq_norm_vsub V X c,
      ← vsub_add_vsub_cancel p X c, norm_add_sq_real, hperp]
    ring
  refine ⟨?_, by linarith⟩
  unfold tangentLength
  rw [dist_comm c p, hpy, sub_zero, add_sub_cancel_right, Real.sqrt_sq dist_nonneg]

end Casey
