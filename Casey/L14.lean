import Casey.Main
import Casey.Bridge

/-!
# Layer 14: Mathlib-only restatement and witness

`l14_casey` states Casey's theorem with the four circles as Mathlib `EuclideanGeometry.Sphere`s,
each internally tangent to `Γ` (Mathlib's `Sphere.IsIntTangentAt`) at `Tᵢ`, and the tangent length
written out as `√(dist cᵢ cⱼ ^ 2 - (rᵢ - rⱼ) ^ 2)`. Its type mentions only Mathlib notions.
`l14_casey_ptolemy` is the zero-radius case (point circles, Mathlib's `Sphere` with radius `0`).
`l14w_casey` instantiates `l14_casey` in `ℂ` with `Γ = (0, 5)`, tangency points `5, 5i, -5, -5i`
and radii `1, 2, 3, 4`; the four circles are pairwise distinct, the tangency points pairwise
distinct, and all six tangent lengths are positive (`t₃₄ = 2`, the others are `√24, √12, √8, √32,
√12`).
-/

open EuclideanGeometry Real

namespace Casey

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- Bridge: a sphere `C` internally tangent to `Γ` at `T` (Mathlib's `IsIntTangentAt`) has centre
`tangentCentre Γ.center T Γ.radius C.radius`, and `C.radius ≤ Γ.radius`. -/
lemma l14_center_of_isIntTangentAt {C Γ : Sphere P} {T : P} (hR : 0 < Γ.radius)
    (h : C.IsIntTangentAt Γ T) :
    C.center = tangentCentre Γ.center T Γ.radius C.radius ∧ C.radius ≤ Γ.radius := by
  obtain ⟨hTC, hTΓ, ⟨t, ⟨ht0, ht1⟩, hc⟩⟩ := h
  have hTO : dist T Γ.center = Γ.radius := EuclideanGeometry.mem_sphere.1 hTΓ
  have hr : dist T C.center = C.radius := EuclideanGeometry.mem_sphere.1 hTC
  rw [← hc, dist_comm, dist_lineMap_right, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), dist_comm, hTO] at hr
  have ht : t = 1 - C.radius / Γ.radius := by
    field_simp
    linarith
  refine ⟨?_, by nlinarith⟩
  rw [← hc, AffineMap.lineMap_apply, ht]
  rfl

/-- **Casey's theorem, Mathlib-only form.** Let `Γ` have positive radius and let `C₁, …, C₄` be
spheres internally tangent to `Γ` at `T₁, …, T₄`, where the diagonals `T₁T₃` and `T₂T₄` meet at a
point `p` strictly between their endpoints. With `tᵢⱼ = √(|cᵢcⱼ|² - (rᵢ - rⱼ)²)` the length of the
common external tangent, `t₁₂ t₃₄ + t₂₃ t₄₁ = t₁₃ t₂₄`. -/
theorem l14_casey (Γ C₁ C₂ C₃ C₄ : Sphere P) {T₁ T₂ T₃ T₄ p : P} (hR : 0 < Γ.radius)
    (h₁ : C₁.IsIntTangentAt Γ T₁) (h₂ : C₂.IsIntTangentAt Γ T₂) (h₃ : C₃.IsIntTangentAt Γ T₃)
    (h₄ : C₄.IsIntTangentAt Γ T₄) (h₁₃ : ∠ T₁ p T₃ = π) (h₂₄ : ∠ T₂ p T₄ = π) :
    √(dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2) *
        √(dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2) +
      √(dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2) *
        √(dist C₄.center C₁.center ^ 2 - (C₄.radius - C₁.radius) ^ 2) =
      √(dist C₁.center C₃.center ^ 2 - (C₁.radius - C₃.radius) ^ 2) *
        √(dist C₂.center C₄.center ^ 2 - (C₂.radius - C₄.radius) ^ 2) := by
  obtain ⟨e₁, l₁⟩ := l14_center_of_isIntTangentAt hR h₁
  obtain ⟨e₂, l₂⟩ := l14_center_of_isIntTangentAt hR h₂
  obtain ⟨e₃, l₃⟩ := l14_center_of_isIntTangentAt hR h₃
  obtain ⟨e₄, l₄⟩ := l14_center_of_isIntTangentAt hR h₄
  have h := casey_of_le hR l₁ l₂ l₃ l₄ (EuclideanGeometry.mem_sphere.1 h₁.mem_right)
    (EuclideanGeometry.mem_sphere.1 h₂.mem_right) (EuclideanGeometry.mem_sphere.1 h₃.mem_right)
    (EuclideanGeometry.mem_sphere.1 h₄.mem_right) h₁₃ h₂₄
  rw [e₁, e₂, e₃, e₄]
  exact h

/-- **Ptolemy as the zero-radius case, Mathlib-only form**: four points of a sphere of positive
radius, with diagonals meeting strictly inside, satisfy Ptolemy's equality. -/
theorem l14_casey_ptolemy (Γ : Sphere P) {T₁ T₂ T₃ T₄ p : P} (hR : 0 < Γ.radius)
    (h₁ : T₁ ∈ Γ) (h₂ : T₂ ∈ Γ) (h₃ : T₃ ∈ Γ) (h₄ : T₄ ∈ Γ)
    (h₁₃ : ∠ T₁ p T₃ = π) (h₂₄ : ∠ T₂ p T₄ = π) :
    dist T₁ T₂ * dist T₃ T₄ + dist T₂ T₃ * dist T₄ T₁ = dist T₁ T₃ * dist T₂ T₄ :=
  casey_zero_radii_eq_ptolemy hR (EuclideanGeometry.mem_sphere.1 h₁)
    (EuclideanGeometry.mem_sphere.1 h₂) (EuclideanGeometry.mem_sphere.1 h₃)
    (EuclideanGeometry.mem_sphere.1 h₄) h₁₃ h₂₄

/-! ### Witness in `ℂ` -/

lemma l14_dist_eq {z w : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = r ^ 2) : dist z w = r := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_sq hr]

lemma l14_dist_sq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

lemma l14_wbtw {x y z : ℂ} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : y = x + (t : ℂ) * (z - x)) : Wbtw ℝ x y z := by
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module, h, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- The witness: `Γ = (0, 5)`, `Cᵢ` of radius `i` tangent at `5, 5i, -5, -5i`, `p = 0`. -/
theorem l14w_casey :
    ∃ (Γ C₁ C₂ C₃ C₄ : Sphere ℂ) (T₁ T₂ T₃ T₄ p : ℂ),
      0 < Γ.radius ∧ C₁.IsIntTangentAt Γ T₁ ∧ C₂.IsIntTangentAt Γ T₂ ∧ C₃.IsIntTangentAt Γ T₃ ∧
      C₄.IsIntTangentAt Γ T₄ ∧ ∠ T₁ p T₃ = π ∧ ∠ T₂ p T₄ = π ∧
      -- non-degeneracy: distinct circles, distinct tangency points, none equal to `Γ`
      C₁ ≠ C₂ ∧ C₁ ≠ C₃ ∧ C₁ ≠ C₄ ∧ C₂ ≠ C₃ ∧ C₂ ≠ C₄ ∧ C₃ ≠ C₄ ∧
      C₁ ≠ Γ ∧ C₂ ≠ Γ ∧ C₃ ≠ Γ ∧ C₄ ≠ Γ ∧ 0 < C₁.radius ∧
      T₁ ≠ T₂ ∧ T₁ ≠ T₃ ∧ T₁ ≠ T₄ ∧ T₂ ≠ T₃ ∧ T₂ ≠ T₄ ∧ T₃ ≠ T₄ ∧
      -- all six tangent lengths are positive (squares `24, 12, 4, 8, 32, 12`)
      dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2 = 24 ∧
      dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2 = 12 ∧
      dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2 = 4 ∧
      dist C₄.center C₁.center ^ 2 - (C₄.radius - C₁.radius) ^ 2 = 8 ∧
      dist C₁.center C₃.center ^ 2 - (C₁.radius - C₃.radius) ^ 2 = 32 ∧
      dist C₂.center C₄.center ^ 2 - (C₂.radius - C₄.radius) ^ 2 = 12 ∧
      -- and the conclusion of `l14_casey`
      √(dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2) *
          √(dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2) +
        √(dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2) *
          √(dist C₄.center C₁.center ^ 2 - (C₄.radius - C₁.radius) ^ 2) =
        √(dist C₁.center C₃.center ^ 2 - (C₁.radius - C₃.radius) ^ 2) *
          √(dist C₂.center C₄.center ^ 2 - (C₂.radius - C₄.radius) ^ 2) := by
  let Γ : Sphere ℂ := ⟨0, 5⟩
  let C₁ : Sphere ℂ := ⟨4, 1⟩
  let C₂ : Sphere ℂ := ⟨3 * Complex.I, 2⟩
  let C₃ : Sphere ℂ := ⟨-2, 3⟩
  let C₄ : Sphere ℂ := ⟨-Complex.I, 4⟩
  have hR : 0 < Γ.radius := by show (0 : ℝ) < 5; norm_num
  have t₁ : C₁.IsIntTangentAt Γ 5 :=
    ⟨EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [C₁])),
     EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [Γ])),
     l14_wbtw (4 / 5) (by norm_num) (by norm_num) (by show (4 : ℂ) = _; push_cast; ring)⟩
  have t₂ : C₂.IsIntTangentAt Γ (5 * Complex.I) :=
    ⟨EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [C₂])),
     EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [Γ])),
     l14_wbtw (3 / 5) (by norm_num) (by norm_num)
       (by show 3 * Complex.I = _; push_cast; ring)⟩
  have t₃ : C₃.IsIntTangentAt Γ (-5) :=
    ⟨EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [C₃])),
     EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [Γ])),
     l14_wbtw (2 / 5) (by norm_num) (by norm_num) (by show (-2 : ℂ) = _; push_cast; ring)⟩
  have t₄ : C₄.IsIntTangentAt Γ (-5 * Complex.I) :=
    ⟨EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [C₄])),
     EuclideanGeometry.mem_sphere.2 (l14_dist_eq (by norm_num) (by norm_num [Γ])),
     l14_wbtw (1 / 5) (by norm_num) (by norm_num)
       (by show -Complex.I = _; push_cast; ring)⟩
  have a₁₃ : ∠ (5 : ℂ) 0 (-5) = π := by
    refine Sbtw.angle₁₂₃_eq_pi ⟨l14_wbtw (1 / 2) (by norm_num) (by norm_num) ?_, ?_, ?_⟩
    · push_cast; ring
    · norm_num
    · norm_num
  have a₂₄ : ∠ (5 * Complex.I) 0 (-5 * Complex.I) = π := by
    refine Sbtw.angle₁₂₃_eq_pi ⟨l14_wbtw (1 / 2) (by norm_num) (by norm_num) ?_, ?_, ?_⟩
    · push_cast; ring
    · simp
    · simp
  have hne : ∀ {a b : Sphere ℂ}, a.radius ≠ b.radius → a ≠ b := fun h e => h (e ▸ rfl)
  have hneI : ∀ {a b : ℂ}, a.im ≠ b.im → a ≠ b := fun h e => h (e ▸ rfl)
  have hneR : ∀ {a b : ℂ}, a.re ≠ b.re → a ≠ b := fun h e => h (e ▸ rfl)
  refine ⟨Γ, C₁, C₂, C₃, C₄, 5, 5 * Complex.I, -5, -5 * Complex.I, 0, hR, t₁, t₂, t₃, t₄,
    a₁₃, a₂₄, ?_⟩
  refine ⟨hne (by show (1 : ℝ) ≠ 2; norm_num), hne (by show (1 : ℝ) ≠ 3; norm_num),
    hne (by show (1 : ℝ) ≠ 4; norm_num), hne (by show (2 : ℝ) ≠ 3; norm_num),
    hne (by show (2 : ℝ) ≠ 4; norm_num), hne (by show (3 : ℝ) ≠ 4; norm_num),
    hne (by show (1 : ℝ) ≠ 5; norm_num), hne (by show (2 : ℝ) ≠ 5; norm_num),
    hne (by show (3 : ℝ) ≠ 5; norm_num), hne (by show (4 : ℝ) ≠ 5; norm_num),
    by show (0 : ℝ) < 1; norm_num,
    hneR (by norm_num), hneR (by norm_num), hneR (by norm_num), hneI (by norm_num), hneI (by norm_num),
    hneR (by norm_num), ?_⟩
  have s₁₂ : dist C₁.center C₂.center ^ 2 - (C₁.radius - C₂.radius) ^ 2 = 24 := by
    rw [l14_dist_sq]; simp [C₁, C₂]; norm_num
  have s₂₃ : dist C₂.center C₃.center ^ 2 - (C₂.radius - C₃.radius) ^ 2 = 12 := by
    rw [l14_dist_sq]; simp [C₂, C₃]; norm_num
  have s₃₄ : dist C₃.center C₄.center ^ 2 - (C₃.radius - C₄.radius) ^ 2 = 4 := by
    rw [l14_dist_sq]; simp [C₃, C₄]; norm_num
  have s₄₁ : dist C₄.center C₁.center ^ 2 - (C₄.radius - C₁.radius) ^ 2 = 8 := by
    rw [l14_dist_sq]; simp [C₄, C₁]; norm_num
  have s₁₃ : dist C₁.center C₃.center ^ 2 - (C₁.radius - C₃.radius) ^ 2 = 32 := by
    rw [l14_dist_sq]; simp [C₁, C₃]; norm_num
  have s₂₄ : dist C₂.center C₄.center ^ 2 - (C₂.radius - C₄.radius) ^ 2 = 12 := by
    rw [l14_dist_sq]; simp [C₂, C₄]; norm_num
  exact ⟨s₁₂, s₂₃, s₃₄, s₄₁, s₁₃, s₂₄, l14_casey Γ C₁ C₂ C₃ C₄ hR t₁ t₂ t₃ t₄ a₁₃ a₂₄⟩

end Casey
