import Mathlib
import Casey.Basic
import Casey.Main
import Casey.Bridge
import Casey.L14

/-!
# Layer 15: comparison with independently written classical statements

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

The writer's theorem statements are packaged as `def classical_X : Prop` (binders turned into `∀`).
-/

open EuclideanGeometry

noncomputable section

namespace Casey.Classical

/-- The Euclidean plane. -/
abbrev Pl := EuclideanSpace ℝ (Fin 2)

/-- OWN DEFINITION. The circle `C` lies in the closed disc of `Γ` and meets `Γ` exactly at
`K`: `C` touches `Γ` internally at `K`. -/
def InternallyTangentAt (C Γ : Sphere Pl) (K : Pl) : Prop :=
  Metric.sphere C.center C.radius ⊆ Metric.closedBall Γ.center Γ.radius ∧
    Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius = {K}

/-- OWN DEFINITION. The closed disc of `C` avoids the open disc of `Γ` (so `C` lies outside
`Γ`, and `Γ` is not inside `C`), and `C` meets `Γ` exactly at `K`: `C` touches `Γ` externally
at `K`. -/
def ExternallyTangentAt (C Γ : Sphere Pl) (K : Pl) : Prop :=
  Disjoint (Metric.closedBall C.center C.radius) (Metric.ball Γ.center Γ.radius) ∧
    Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius = {K}

/-- OWN DEFINITION. Two circles are tangent: they have exactly one common point
(for a point-circle this means the point lies on the other circle). -/
def CirclesTangent (C D : Sphere Pl) : Prop :=
  ∃! p : Pl, p ∈ Metric.sphere C.center C.radius ∧ p ∈ Metric.sphere D.center D.radius

/-- OWN DEFINITION. A line (affine subspace) is tangent to a circle: exactly one common
point. -/
def LineTangent (L : AffineSubspace ℝ Pl) (C : Sphere Pl) : Prop :=
  ∃! p : Pl, p ∈ L ∧ p ∈ Metric.sphere C.center C.radius

/-- OWN DEFINITION. Four points `K 0, K 1, K 2, K 3` (assumed on a common circle) occur in
this cyclic order: they are pairwise distinct and the chords `K0K2`, `K1K3` meet. -/
def CyclicOrder4 (K : Fin 4 → Pl) : Prop :=
  Function.Injective K ∧ (segment ℝ (K 0) (K 2) ∩ segment ℝ (K 1) (K 3)).Nonempty

/-- Length of the direct common tangent of two circles (formula from the problem statement). -/
def directTangent (C D : Sphere Pl) : ℝ :=
  Real.sqrt (dist C.center D.center ^ 2 - (C.radius - D.radius) ^ 2)

/-- Signed-radius tangent length `sqrt(|O_iO_j|^2 - (ρ_i - ρ_j)^2)`. -/
def signedTangent (C D : Sphere Pl) (ρC ρD : ℝ) : ℝ :=
  Real.sqrt (dist C.center D.center ^ 2 - (ρC - ρD) ^ 2)

/-- OWN DEFINITION. `ABCD` is a convex (non-degenerate) quadrilateral: the diagonals `AC`
and `BD` cross at a point strictly inside both, and no three vertices are collinear. -/
def ConvexQuad (A B C D : Pl) : Prop :=
  (∃ X : Pl, Sbtw ℝ A X C ∧ Sbtw ℝ B X D) ∧
    ¬ Collinear ℝ {A, B, C} ∧ ¬ Collinear ℝ {B, C, D} ∧
    ¬ Collinear ℝ {C, D, A} ∧ ¬ Collinear ℝ {D, A, B}

/-- OWN DEFINITION. The circle `ω` is tangent to the side (segment) `PQ`: the whole line
`PQ` stays at distance `≥ r` from the centre and the touching point lies on the segment. -/
def TangentToSide (ω : Sphere Pl) (P Q : Pl) : Prop :=
  (∃ T : Pl, Wbtw ℝ P T Q ∧ dist T ω.center = ω.radius) ∧
    ∀ Y ∈ line[ℝ, P, Q], ω.radius ≤ dist Y ω.center

/-- OWN DEFINITION. `ω` (radius `> 0`) is an incircle of the quadrilateral `ABCD`:
it touches all four sides. -/
def IsIncircleQuad (ω : Sphere Pl) (A B C D : Pl) : Prop :=
  0 < ω.radius ∧ TangentToSide ω A B ∧ TangentToSide ω B C ∧
    TangentToSide ω C D ∧ TangentToSide ω D A

/-- OWN DEFINITION. `ABCD` is a convex quadrilateral inscribed in `Γ` and circumscribed
about `ω` (bicentric with these circles). -/
def BicentricWith (Γ ω : Sphere Pl) (A B C D : Pl) : Prop :=
  ConvexQuad A B C D ∧ A ∈ Γ ∧ B ∈ Γ ∧ C ∈ Γ ∧ D ∈ Γ ∧ IsIncircleQuad ω A B C D

/-- OWN DEFINITION. The circle `ω` lies strictly inside the circle `Γ`
(`ω` a genuine circle, `r > 0`). -/
def StrictlyInside (ω Γ : Sphere Pl) : Prop :=
  0 < ω.radius ∧ dist ω.center Γ.center + ω.radius < Γ.radius

/-- Writer's statement `classical_CaseyFuss1_a_obligation`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss1_a_obligation : Prop :=
  ∀ (Γ : Sphere Pl) (C : Fin 4 → Sphere Pl)
    (K : Fin 4 → Pl) (hR : 0 < Γ.radius) (hr : ∀ i, 0 ≤ (C i).radius)
    (htan : ∀ i, InternallyTangentAt (C i) Γ (K i)) (hord : CyclicOrder4 K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.sphere (C i).center (C i).radius)
      (Metric.sphere (C j).center (C j).radius)) (i j : Fin 4),
    ((C i).radius - (C j).radius) ^ 2 ≤ dist (C i).center (C j).center ^ 2 

/-- Writer's statement `classical_CaseyFuss1_a`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss1_a : Prop :=
  ∀ (Γ : Sphere Pl) (C : Fin 4 → Sphere Pl) (K : Fin 4 → Pl)
    (hR : 0 < Γ.radius) (hr : ∀ i, 0 ≤ (C i).radius)
    (htan : ∀ i, InternallyTangentAt (C i) Γ (K i)) (hord : CyclicOrder4 K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Metric.sphere (C i).center (C i).radius)
      (Metric.sphere (C j).center (C j).radius)),
    directTangent (C 0) (C 1) * directTangent (C 2) (C 3) +
        directTangent (C 0) (C 3) * directTangent (C 1) (C 2) =
      directTangent (C 0) (C 2) * directTangent (C 1) (C 3) 

/-- Writer's statement `classical_CaseyFuss1_b_obligation`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss1_b_obligation : Prop :=
  ∀ (Γ : Sphere Pl) (C : Fin 4 → Sphere Pl)
    (K : Fin 4 → Pl) (ρ : Fin 4 → ℝ) (hR : 0 < Γ.radius) (hr : ∀ i, 0 ≤ (C i).radius)
    (htan : ∀ i, (InternallyTangentAt (C i) Γ (K i) ∧ ρ i = (C i).radius) ∨
      (ExternallyTangentAt (C i) Γ (K i) ∧ ρ i = -(C i).radius))
    (hord : CyclicOrder4 K) (i j : Fin 4),
    (ρ i - ρ j) ^ 2 ≤ dist (C i).center (C j).center ^ 2 ∧
      0 ≤ (Γ.radius - ρ i) * (Γ.radius - ρ j) 

/-- Writer's statement `classical_CaseyFuss1_b`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss1_b : Prop :=
  ∀ (Γ : Sphere Pl) (C : Fin 4 → Sphere Pl) (K : Fin 4 → Pl)
    (ρ : Fin 4 → ℝ) (hR : 0 < Γ.radius) (hr : ∀ i, 0 ≤ (C i).radius)
    (htan : ∀ i, (InternallyTangentAt (C i) Γ (K i) ∧ ρ i = (C i).radius) ∨
      (ExternallyTangentAt (C i) Γ (K i) ∧ ρ i = -(C i).radius))
    (hord : CyclicOrder4 K),
    (∀ i j, signedTangent (C i) (C j) (ρ i) (ρ j) =
        dist (K i) (K j) * Real.sqrt ((Γ.radius - ρ i) * (Γ.radius - ρ j)) / Γ.radius) ∧
      signedTangent (C 0) (C 1) (ρ 0) (ρ 1) * signedTangent (C 2) (C 3) (ρ 2) (ρ 3) +
          signedTangent (C 0) (C 3) (ρ 0) (ρ 3) * signedTangent (C 1) (C 2) (ρ 1) (ρ 2) =
        signedTangent (C 0) (C 2) (ρ 0) (ρ 2) * signedTangent (C 1) (C 3) (ρ 1) (ρ 3) 

/-- Writer's statement `classical_CaseyFuss1_c`, verbatim (binders turned into `∀`). -/
def classical_CaseyFuss1_c : Prop :=
  ∀ (C : Fin 4 → Sphere Pl) (hr : ∀ i, 0 ≤ (C i).radius)
    (ε : Fin 4 → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hex : ∀ i j, (ε i * (C i).radius - ε j * (C j).radius) ^ 2 ≤
      dist (C i).center (C j).center ^ 2)
    (s₁ s₂ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (hrel : let t := fun i j => signedTangent (C i) (C j) (ε i * (C i).radius) (ε j * (C j).radius)
      t 0 1 * t 2 3 + s₁ * (t 0 2 * t 1 3) + s₂ * (t 0 3 * t 1 2) = 0),
    (∃ Γ : Sphere Pl, 0 < Γ.radius ∧ ∀ i, CirclesTangent (C i) Γ) ∨
      (∃ p q : Pl, p ≠ q ∧ ∀ i, LineTangent line[ℝ, p, q] (C i)) 

/-! ## Bridge lemmas (NEW) -/

/-- A centre at distance `|R - ρ|` from `O` and `|ρ|` from the tangency point `K ∈ Γ(O, R)` is
`Casey.tangentCentre O K R ρ`. -/
theorem tc_eq {O K c : Pl} {R ρ : ℝ} (hR : R ≠ 0) (hK : dist K O = R)
    (hc : dist c O ^ 2 = (R - ρ) ^ 2) (hKc : dist K c ^ 2 = ρ ^ 2) :
    c = Casey.tangentCentre O K R ρ := by
  unfold Casey.tangentCentre
  rw [eq_vadd_iff_vsub_eq, vsub_eq_sub, vsub_eq_sub]
  set a := 1 - ρ / R with ha_def
  have ha : a * R = R - ρ := by rw [ha_def]; field_simp
  set u := K - O
  set w := c - O
  have hu : ‖u‖ = R := by rw [← dist_eq_norm]; exact hK
  have hu2 : ‖u‖ ^ 2 = R ^ 2 := by rw [hu]
  have hw : ‖w‖ ^ 2 = (R - ρ) ^ 2 := by rw [← dist_eq_norm]; exact hc
  have huw : ‖u - w‖ ^ 2 = ρ ^ 2 := by
    have : u - w = K - c := sub_sub_sub_cancel_right K c O
    rw [this, ← dist_eq_norm]; exact hKc
  rw [norm_sub_sq_real, hu] at huw
  have hY : inner ℝ w u = R * (R - ρ) := by
    rw [real_inner_comm]; linear_combination (-1 / 2 : ℝ) * huw + (1 / 2 : ℝ) * hw
  have h0 : ‖w - a • u‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    linear_combination hw - 2 * a * hY + a ^ 2 * hu2 + (a * R - (R - ρ)) * ha
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))

/-- Internal tangency in the writer's sense gives the classical distances. -/
theorem int_dist {Γ C : Sphere Pl} {K : Pl} (hR : 0 < Γ.radius) (hr : 0 ≤ C.radius)
    (h : InternallyTangentAt C Γ K) :
    dist C.center Γ.center = Γ.radius - C.radius ∧ dist K C.center = C.radius ∧
      dist K Γ.center = Γ.radius := by
  obtain ⟨hsub, hint⟩ := h
  have hK : K ∈ Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius := by
    rw [hint]; rfl
  have hKc : dist K C.center = C.radius := hK.1
  have hKO : dist K Γ.center = Γ.radius := hK.2
  refine ⟨?_, hKc, hKO⟩
  have h1 : Γ.radius ≤ C.radius + dist C.center Γ.center := by
    rw [← hKO, ← hKc]; exact dist_triangle _ _ _
  set D := dist C.center Γ.center with hD
  by_cases hc0 : C.center = Γ.center
  · have : D = 0 := by rw [hD, hc0, dist_self]
    rw [hc0] at hKc
    linarith
  have hDpos : 0 < D := dist_pos.2 hc0
  set q : Pl := C.center + (C.radius / D) • (C.center - Γ.center)
  have hq1 : dist q C.center = C.radius := by
    rw [dist_eq_norm, show q - C.center = (C.radius / D) • (C.center - Γ.center) by
      simp only [q]; abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hDpos.le),
      ← dist_eq_norm, ← hD, div_mul_cancel₀ _ hDpos.ne']
  have hq2 : dist q Γ.center = D + C.radius := by
    rw [dist_eq_norm, show q - Γ.center = (1 + C.radius / D) • (C.center - Γ.center) by
      rw [add_smul, one_smul]; simp only [q]; abel, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), ← dist_eq_norm, ← hD, add_mul, one_mul,
      div_mul_cancel₀ _ hDpos.ne']
  have hq : q ∈ Metric.closedBall Γ.center Γ.radius := hsub hq1
  rw [Metric.mem_closedBall, hq2] at hq
  linarith

/-- External tangency in the writer's sense gives the classical distances. -/
theorem ext_dist {Γ C : Sphere Pl} {K : Pl} (hR : 0 < Γ.radius) (hr : 0 ≤ C.radius)
    (h : ExternallyTangentAt C Γ K) :
    dist C.center Γ.center = Γ.radius + C.radius ∧ dist K C.center = C.radius ∧
      dist K Γ.center = Γ.radius := by
  obtain ⟨hdisj, hint⟩ := h
  have hK : K ∈ Metric.sphere C.center C.radius ∩ Metric.sphere Γ.center Γ.radius := by
    rw [hint]; rfl
  have hKc : dist K C.center = C.radius := hK.1
  have hKO : dist K Γ.center = Γ.radius := hK.2
  refine ⟨?_, hKc, hKO⟩
  set D := dist C.center Γ.center with hD
  have h1 : D ≤ C.radius + Γ.radius := by
    rw [hD, ← hKO, ← hKc, dist_comm K C.center]; exact dist_triangle _ _ _
  by_contra hne
  have hlt : D < Γ.radius + C.radius := lt_of_le_of_ne (by linarith) hne
  by_cases hDr : D ≤ C.radius
  · have hO1 : Γ.center ∈ Metric.closedBall C.center C.radius := by
      rw [Metric.mem_closedBall, dist_comm]; exact hDr
    have hO2 : Γ.center ∈ Metric.ball Γ.center Γ.radius := Metric.mem_ball_self hR
    exact Set.disjoint_left.1 hdisj hO1 hO2
  push_neg at hDr
  have hDpos : 0 < D := lt_of_le_of_lt hr hDr
  set q : Pl := C.center + (C.radius / D) • (Γ.center - C.center)
  have hq1 : dist q C.center = C.radius := by
    rw [dist_eq_norm, show q - C.center = (C.radius / D) • (Γ.center - C.center) by
      simp only [q]; abel, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hDpos.le),
      ← dist_eq_norm, dist_comm, ← hD, div_mul_cancel₀ _ hDpos.ne']
  have hq2 : dist q Γ.center = D - C.radius := by
    have hcoef : 0 ≤ 1 - C.radius / D := by
      rw [sub_nonneg, div_le_one hDpos]; exact hDr.le
    rw [dist_eq_norm, show q - Γ.center = (1 - C.radius / D) • (C.center - Γ.center) by
      rw [sub_smul, one_smul, ← neg_sub Γ.center C.center, smul_neg]; simp only [q]; abel,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef, ← dist_eq_norm, ← hD, sub_mul, one_mul,
      div_mul_cancel₀ _ hDpos.ne']
  have hq1' : q ∈ Metric.closedBall C.center C.radius := by
    rw [Metric.mem_closedBall, hq1]
  have hq2' : q ∈ Metric.ball Γ.center Γ.radius := by
    rw [Metric.mem_ball, hq2]; linarith
  exact Set.disjoint_left.1 hdisj hq1' hq2'

/-- Signed-radius bridge: either tangency type gives `centre = tangentCentre O K R ρ`, `ρ ≤ R`. -/
theorem signed_bridge {Γ C : Sphere Pl} {K : Pl} {ρ : ℝ} (hR : 0 < Γ.radius)
    (hr : 0 ≤ C.radius)
    (h : (InternallyTangentAt C Γ K ∧ ρ = C.radius) ∨
      (ExternallyTangentAt C Γ K ∧ ρ = -C.radius)) :
    C.center = Casey.tangentCentre Γ.center K Γ.radius ρ ∧ ρ ≤ Γ.radius ∧
      dist K Γ.center = Γ.radius := by
  rcases h with ⟨hi, rfl⟩ | ⟨he, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := int_dist hR hr hi
    refine ⟨tc_eq hR.ne' h3 (by rw [h1]) (by rw [h2]), ?_, h3⟩
    linarith [dist_nonneg (x := C.center) (y := Γ.center)]
  · obtain ⟨h1, h2, h3⟩ := ext_dist hR hr he
    refine ⟨tc_eq hR.ne' h3 (by rw [h1]; ring) (by rw [h2]; ring), by linarith, h3⟩

/-- A point of a circle is not strictly between two other points of it. -/
theorem no_mid {a b c O : Pl} {R : ℝ} (ha : dist a O = R) (hb : dist b O = R)
    (hc : dist c O = R) (h : Wbtw ℝ a b c) (hba : b ≠ a) (hbc : b ≠ c) : False := by
  have := Sbtw.dist_lt_max_dist O ⟨h, hba, hbc⟩
  rw [ha, hb, hc, max_self] at this
  exact lt_irrefl _ this

/-- The writer's `CyclicOrder4` on a circle gives Mathlib/Casey's angle form of cyclic order. -/
theorem cyc_angles {O : Pl} {R : ℝ} {K : Fin 4 → Pl} (hK : ∀ i, dist (K i) O = R)
    (hord : CyclicOrder4 K) : ∃ p, ∠ (K 0) p (K 2) = Real.pi ∧ ∠ (K 1) p (K 3) = Real.pi := by
  obtain ⟨hinj, p, hp1, hp2⟩ := hord
  rw [mem_segment_iff_wbtw] at hp1 hp2
  have n : ∀ i j : Fin 4, i ≠ j → K i ≠ K j := fun i j h => hinj.ne h
  refine ⟨p, Sbtw.angle₁₂₃_eq_pi ⟨hp1, ?_, ?_⟩, Sbtw.angle₁₂₃_eq_pi ⟨hp2, ?_, ?_⟩⟩
  · rintro rfl; exact no_mid (hK 1) (hK 0) (hK 3) hp2 (n 0 1 (by decide)) (n 0 3 (by decide))
  · rintro rfl; exact no_mid (hK 1) (hK 2) (hK 3) hp2 (n 2 1 (by decide)) (n 2 3 (by decide))
  · rintro rfl; exact no_mid (hK 0) (hK 1) (hK 2) hp1 (n 1 0 (by decide)) (n 1 2 (by decide))
  · rintro rfl; exact no_mid (hK 0) (hK 3) (hK 2) hp1 (n 3 0 (by decide)) (n 3 2 (by decide))

/-! ## Covering theorems -/

/-- Signed form, general: from the bridge data, Casey's relation for `signedTangent`. -/
theorem casey_signed {Γ : Sphere Pl} {C : Fin 4 → Sphere Pl} {K : Fin 4 → Pl} {ρ : Fin 4 → ℝ}
    (hR : 0 < Γ.radius)
    (hc : ∀ i, (C i).center = Casey.tangentCentre Γ.center (K i) Γ.radius (ρ i))
    (hle : ∀ i, ρ i ≤ Γ.radius) (hK : ∀ i, dist (K i) Γ.center = Γ.radius)
    (hord : CyclicOrder4 K) :
    signedTangent (C 0) (C 1) (ρ 0) (ρ 1) * signedTangent (C 2) (C 3) (ρ 2) (ρ 3) +
        signedTangent (C 0) (C 3) (ρ 0) (ρ 3) * signedTangent (C 1) (C 2) (ρ 1) (ρ 2) =
      signedTangent (C 0) (C 2) (ρ 0) (ρ 2) * signedTangent (C 1) (C 3) (ρ 1) (ρ 3) := by
  obtain ⟨p, h13, h24⟩ := cyc_angles hK hord
  have key := Casey.casey_of_le hR (hle 0) (hle 1) (hle 2) (hle 3) (hK 0) (hK 1) (hK 2) (hK 3)
    h13 h24
  rw [Casey.tangentLength_comm (Casey.tangentCentre _ (K 3) _ _)] at key
  have e : ∀ i j, signedTangent (C i) (C j) (ρ i) (ρ j) = Casey.tangentLength
      (Casey.tangentCentre Γ.center (K i) Γ.radius (ρ i))
      (Casey.tangentCentre Γ.center (K j) Γ.radius (ρ j)) (ρ i) (ρ j) := by
    intro i j; unfold signedTangent Casey.tangentLength; rw [hc i, hc j]
  rw [e 0 1, e 2 3, e 0 3, e 1 2, e 0 2, e 1 3]
  linear_combination key

theorem cov_CaseyFuss1_a : classical_CaseyFuss1_a := by
  intro Γ C K hR hr htan hord _hdisj
  have hb := fun i => signed_bridge (ρ := (C i).radius) hR (hr i) (Or.inl ⟨htan i, rfl⟩)
  exact casey_signed (ρ := fun i => (C i).radius) hR (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i => (hb i).2.2) hord

theorem cov_CaseyFuss1_b : classical_CaseyFuss1_b := by
  intro Γ C K ρ hR hr htan hord
  have hb := fun i => signed_bridge hR (hr i) (htan i)
  refine ⟨fun i j => ?_, casey_signed hR (fun i => (hb i).1) (fun i => (hb i).2.1)
    (fun i => (hb i).2.2) hord⟩
  have := Casey.tangentLength_tangentCentre hR (hb i).2.1 (hb j).2.1 (hb i).2.2 (hb j).2.2
  unfold Casey.tangentLength at this
  unfold signedTangent
  rw [(hb i).1, (hb j).1, this, Real.sqrt_mul (sub_nonneg.2 (hb i).2.1)]

/-- Radicand nonnegativity from the key lemma. -/
theorem radicand_nonneg {O K₁ K₂ : Pl} {R r₁ r₂ : ℝ} (hR : 0 < R) (h₁ : dist K₁ O = R)
    (h₂ : dist K₂ O = R) (hr₁ : r₁ ≤ R) (hr₂ : r₂ ≤ R) :
    (r₁ - r₂) ^ 2 ≤ dist (Casey.tangentCentre O K₁ R r₁) (Casey.tangentCentre O K₂ R r₂) ^ 2 := by
  have := Casey.dist_tangentCentre_sq_sub_sq r₁ r₂ hR.ne' h₁ h₂
  have : 0 ≤ dist K₁ K₂ ^ 2 * ((R - r₁) * (R - r₂)) / R ^ 2 :=
    div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))) (sq_nonneg _)
  linarith

theorem cov_CaseyFuss1_a_obligation : classical_CaseyFuss1_a_obligation := by
  intro Γ C K hR hr htan _hord _hdisj i j
  have hb := fun i => signed_bridge (ρ := (C i).radius) hR (hr i) (Or.inl ⟨htan i, rfl⟩)
  rw [(hb i).1, (hb j).1]
  exact radicand_nonneg hR (hb i).2.2 (hb j).2.2 (hb i).2.1 (hb j).2.1

theorem cov_CaseyFuss1_b_obligation : classical_CaseyFuss1_b_obligation := by
  intro Γ C K ρ hR hr htan _hord i j
  have hb := fun i => signed_bridge hR (hr i) (htan i)
  refine ⟨?_, mul_nonneg (sub_nonneg.2 (hb i).2.1) (sub_nonneg.2 (hb j).2.1)⟩
  rw [(hb i).1, (hb j).1]
  exact radicand_nonneg hR (hb i).2.2 (hb j).2.2 (hb i).2.1 (hb j).2.1

/-! ## CaseyFuss1 (c): the statement as written is false -/

-- The writer's statement `classical_CaseyFuss1_c` is false as written.
/-- Counterexample: `C₀` the unit circle, `C₁` the point `(1,0)`, `C₂ = C₃` the point `(-1,0)`
(point-circles on `C₀`), all signs `+1`. Then `t₀₁ = t₀₂ = t₀₃ = 0`, so the relation holds,
but no circle or line meets `C₀` in exactly one point while passing through both points. -/
theorem not_classical_CaseyFuss1_c : ¬ classical_CaseyFuss1_c := by
  intro h
  set P1 : Pl := EuclideanSpace.single 0 1 with hP1d
  set P2 : Pl := EuclideanSpace.single 0 (-1) with hP2d
  have hP1 : ‖P1‖ = 1 := by rw [hP1d, PiLp.norm_single, norm_one]
  have hP2 : ‖P2‖ = 1 := by rw [hP2d, PiLp.norm_single, norm_neg, norm_one]
  have hne : P1 ≠ P2 := by
    intro e
    have := congrArg (fun v : Pl => v 0) e
    simp [P1, P2] at this
    norm_num at this
  let C : Fin 4 → Sphere Pl := ![⟨0, 1⟩, ⟨P1, 0⟩, ⟨P2, 0⟩, ⟨P2, 0⟩]
  have hz : ∀ P : Pl, ‖P‖ = 1 →
      signedTangent ⟨0, 1⟩ ⟨P, 0⟩ (1 * 1) (1 * 0) = 0 := by
    intro P hP
    simp [signedTangent, dist_zero_left, hP]
  have hres := h C (by intro i; fin_cases i <;> simp [C]) (fun _ => 1) (fun _ => Or.inl rfl)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [C, dist_zero_left, dist_zero_right, hP1, hP2, sq_nonneg])
    1 1 (Or.inl rfl) (Or.inl rfl)
    (by
      dsimp only
      have h1 : signedTangent (C 0) (C 1) (1 * (C 0).radius) (1 * (C 1).radius) = 0 := hz P1 hP1
      have h2 : signedTangent (C 0) (C 2) (1 * (C 0).radius) (1 * (C 2).radius) = 0 := hz P2 hP2
      have h3 : signedTangent (C 0) (C 3) (1 * (C 0).radius) (1 * (C 3).radius) = 0 := hz P2 hP2
      rw [h1, h2, h3]; ring)
  have m1 : P1 ∈ Metric.sphere (0 : Pl) 1 := by rw [mem_sphere_zero_iff_norm]; exact hP1
  have m2 : P2 ∈ Metric.sphere (0 : Pl) 1 := by rw [mem_sphere_zero_iff_norm]; exact hP2
  rcases hres with ⟨Γ, -, hΓ⟩ | ⟨p, q, -, hL⟩
  · have g : ∀ x : Pl, CirclesTangent ⟨x, 0⟩ Γ → x ∈ Metric.sphere Γ.center Γ.radius := by
      rintro x ⟨y, ⟨hy1, hy2⟩, -⟩
      rw [Metric.sphere_zero, Set.mem_singleton_iff] at hy1
      rwa [hy1] at hy2
    have a1 := g P1 (hΓ 1)
    have a2 := g P2 (hΓ 2)
    obtain ⟨y, -, hu⟩ := hΓ 0
    exact hne ((hu P1 ⟨m1, a1⟩).trans (hu P2 ⟨m2, a2⟩).symm)
  · have g : ∀ x : Pl, LineTangent line[ℝ, p, q] ⟨x, 0⟩ → x ∈ line[ℝ, p, q] := by
      rintro x ⟨y, ⟨hy1, hy2⟩, -⟩
      rw [Metric.sphere_zero, Set.mem_singleton_iff] at hy2
      rwa [hy2] at hy1
    have a1 := g P1 (hL 1)
    have a2 := g P2 (hL 2)
    obtain ⟨y, -, hu⟩ := hL 0
    exact hne ((hu P1 ⟨a1, m1⟩).trans (hu P2 ⟨a2, m2⟩).symm)

end Casey.Classical
