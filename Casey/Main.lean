/-
# Casey's theorem (generalized Ptolemy theorem)

Let `Γ` be the circle with centre `O` and radius `R > 0` and let `T₁, T₂, T₃, T₄ ∈ Γ` be in
cyclic order, expressed (as in Mathlib's Ptolemy theorem) by the diagonals `T₁T₃` and `T₂T₄`
meeting at a point `p` strictly between their endpoints: `∠ T₁ p T₃ = π`, `∠ T₂ p T₄ = π`.
Let `Cᵢ` be the circle of radius `rᵢ` internally tangent to `Γ` at `Tᵢ` (so `0 ≤ rᵢ < R`,
`rᵢ = 0` meaning the point `Tᵢ`), with centre `cᵢ = tangentCentre O Tᵢ R rᵢ`, and let
`tᵢⱼ = √(dist cᵢ cⱼ ² - (rᵢ - rⱼ)²)` be the length of the common external tangent.
Then `t₁₂ t₃₄ + t₂₃ t₄₁ = t₁₃ t₂₄`.

The general version `casey_of_le` only assumes `rᵢ ≤ R`; with `rᵢ < 0` the circle of radius
`|rᵢ|` is externally tangent to `Γ` at `Tᵢ`, and `tᵢⱼ` is then the length of the appropriate
common tangent (internal tangent between an internally and an externally tangent circle).
-/
import Casey.Basic

namespace Casey

open EuclideanGeometry Real

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

theorem cospherical_of_dist_eq {O T₁ T₂ T₃ T₄ : P} {R : ℝ} (h₁ : dist T₁ O = R)
    (h₂ : dist T₂ O = R) (h₃ : dist T₃ O = R) (h₄ : dist T₄ O = R) :
    Cospherical ({T₁, T₂, T₃, T₄} : Set P) := by
  refine ⟨O, R, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro p (rfl | rfl | rfl | rfl) <;> assumption

/-- **Casey's theorem**, general signed-radius form: only `rᵢ ≤ R` is required (negative
`rᵢ` encodes a circle externally tangent to `Γ`). -/
theorem casey_of_le {O T₁ T₂ T₃ T₄ p : P} {R r₁ r₂ r₃ r₄ : ℝ} (hR : 0 < R)
    (hr₁ : r₁ ≤ R) (hr₂ : r₂ ≤ R) (hr₃ : r₃ ≤ R) (hr₄ : r₄ ≤ R)
    (h₁ : dist T₁ O = R) (h₂ : dist T₂ O = R) (h₃ : dist T₃ O = R) (h₄ : dist T₄ O = R)
    (h₁₃ : ∠ T₁ p T₃ = π) (h₂₄ : ∠ T₂ p T₄ = π) :
    tangentLength (tangentCentre O T₁ R r₁) (tangentCentre O T₂ R r₂) r₁ r₂ *
        tangentLength (tangentCentre O T₃ R r₃) (tangentCentre O T₄ R r₄) r₃ r₄ +
      tangentLength (tangentCentre O T₂ R r₂) (tangentCentre O T₃ R r₃) r₂ r₃ *
        tangentLength (tangentCentre O T₄ R r₄) (tangentCentre O T₁ R r₁) r₄ r₁ =
      tangentLength (tangentCentre O T₁ R r₁) (tangentCentre O T₃ R r₃) r₁ r₃ *
        tangentLength (tangentCentre O T₂ R r₂) (tangentCentre O T₄ R r₄) r₂ r₄ := by
  have hP := mul_dist_add_mul_dist_eq_mul_dist_of_cospherical
    (cospherical_of_dist_eq h₁ h₂ h₃ h₄) h₁₃ h₂₄
  rw [tangentLength_tangentCentre hR hr₁ hr₂ h₁ h₂, tangentLength_tangentCentre hR hr₃ hr₄ h₃ h₄,
    tangentLength_tangentCentre hR hr₂ hr₃ h₂ h₃, tangentLength_tangentCentre hR hr₄ hr₁ h₄ h₁,
    tangentLength_tangentCentre hR hr₁ hr₃ h₁ h₃, tangentLength_tangentCentre hR hr₂ hr₄ h₂ h₄]
  have key : ∀ a b c d : ℝ,
      dist T₁ T₂ * (a * b) / R * (dist T₃ T₄ * (c * d) / R) +
          dist T₂ T₃ * (b * c) / R * (dist T₄ T₁ * (d * a) / R) =
        (dist T₁ T₂ * dist T₃ T₄ + dist T₂ T₃ * dist T₄ T₁) * (a * b * c * d) / R ^ 2 := by
    intro a b c d
    field_simp
  rw [key, hP]
  field_simp

/-- **Casey's theorem** (generalized Ptolemy theorem). Four circles of radii `0 ≤ rᵢ < R`
internally tangent to the circle `Γ(O, R)` at `T₁, T₂, T₃, T₄` in cyclic order satisfy
`t₁₂ t₃₄ + t₂₃ t₄₁ = t₁₃ t₂₄`, where `tᵢⱼ` is the length of the common external tangent. -/
theorem casey {O T₁ T₂ T₃ T₄ p : P} {R r₁ r₂ r₃ r₄ : ℝ} (hR : 0 < R)
    (hr₁ : 0 ≤ r₁ ∧ r₁ < R) (hr₂ : 0 ≤ r₂ ∧ r₂ < R) (hr₃ : 0 ≤ r₃ ∧ r₃ < R)
    (hr₄ : 0 ≤ r₄ ∧ r₄ < R)
    (h₁ : dist T₁ O = R) (h₂ : dist T₂ O = R) (h₃ : dist T₃ O = R) (h₄ : dist T₄ O = R)
    (h₁₃ : ∠ T₁ p T₃ = π) (h₂₄ : ∠ T₂ p T₄ = π) :
    tangentLength (tangentCentre O T₁ R r₁) (tangentCentre O T₂ R r₂) r₁ r₂ *
        tangentLength (tangentCentre O T₃ R r₃) (tangentCentre O T₄ R r₄) r₃ r₄ +
      tangentLength (tangentCentre O T₂ R r₂) (tangentCentre O T₃ R r₃) r₂ r₃ *
        tangentLength (tangentCentre O T₄ R r₄) (tangentCentre O T₁ R r₁) r₄ r₁ =
      tangentLength (tangentCentre O T₁ R r₁) (tangentCentre O T₃ R r₃) r₁ r₃ *
        tangentLength (tangentCentre O T₂ R r₂) (tangentCentre O T₄ R r₄) r₂ r₄ :=
  casey_of_le hR hr₁.2.le hr₂.2.le hr₃.2.le hr₄.2.le h₁ h₂ h₃ h₄ h₁₃ h₂₄

/-- Sanity check: the circles `Cᵢ` really are internally tangent to `Γ` at `Tᵢ`: the centre
`cᵢ` is at distance `R - rᵢ` from `O`, and `Tᵢ` is at distance `rᵢ` from `cᵢ`. -/
theorem tangentCentre_spec {O T : P} {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r ∧ r < R)
    (hT : dist T O = R) :
    dist (tangentCentre O T R r) O = R - r ∧ dist T (tangentCentre O T R r) = r := by
  refine ⟨by rw [dist_tangentCentre_center r hR.ne' hT, abs_of_pos (sub_pos.2 hr.2)], ?_⟩
  unfold tangentCentre
  rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← one_smul ℝ (T -ᵥ O), smul_smul, mul_one,
    ← sub_smul, norm_smul, ← dist_eq_norm_vsub V, hT, Real.norm_eq_abs]
  have : (1 : ℝ) - (1 - r / R) = r / R := by ring
  rw [this, abs_of_nonneg (div_nonneg hr.1 hR.le)]
  field_simp

/-- Sanity check for the signed-radius convention of `casey_of_le`: for `r ≤ 0` the circle of
radius `-r` centred at `tangentCentre O T R r` is externally tangent to `Γ` at `T`: its centre is
at distance `R + (-r)` from `O` and `T` is at distance `-r` from it. -/
theorem tangentCentre_spec_external {O T : P} {R r : ℝ} (hR : 0 < R) (hr : r ≤ 0)
    (hT : dist T O = R) :
    dist (tangentCentre O T R r) O = R + -r ∧ dist T (tangentCentre O T R r) = -r := by
  refine ⟨by rw [dist_tangentCentre_center r hR.ne' hT, abs_of_pos (by linarith)]; ring, ?_⟩
  unfold tangentCentre
  rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, ← one_smul ℝ (T -ᵥ O), smul_smul, mul_one,
    ← sub_smul, norm_smul, ← dist_eq_norm_vsub V, hT, Real.norm_eq_abs]
  have : (1 : ℝ) - (1 - r / R) = r / R := by ring
  rw [this, abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr hR.le)]
  field_simp

/-- **Degenerate case**: with all radii `0`, Casey's theorem is exactly Ptolemy's theorem. -/
theorem casey_zero_radii_eq_ptolemy {O T₁ T₂ T₃ T₄ p : P} {R : ℝ} (hR : 0 < R)
    (h₁ : dist T₁ O = R) (h₂ : dist T₂ O = R) (h₃ : dist T₃ O = R) (h₄ : dist T₄ O = R)
    (h₁₃ : ∠ T₁ p T₃ = π) (h₂₄ : ∠ T₂ p T₄ = π) :
    dist T₁ T₂ * dist T₃ T₄ + dist T₂ T₃ * dist T₄ T₁ = dist T₁ T₃ * dist T₂ T₄ := by
  have h := casey (r₁ := 0) (r₂ := 0) (r₃ := 0) (r₄ := 0) hR ⟨le_rfl, hR⟩ ⟨le_rfl, hR⟩
    ⟨le_rfl, hR⟩ ⟨le_rfl, hR⟩ h₁ h₂ h₃ h₄ h₁₃ h₂₄
  simpa only [tangentCentre_zero, tangentLength_zero] using h

end Casey
