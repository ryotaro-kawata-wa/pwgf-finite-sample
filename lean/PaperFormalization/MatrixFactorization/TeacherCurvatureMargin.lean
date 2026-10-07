import PaperFormalization.MatrixFactorization.GeneralRetractionObjective

/-! # A uniform positive scalar margin near positive teacher transport

The constants are proof-local. The resulting radius and margin prove the
source existential neighborhood statement without asserting its auxiliary
sharper continuity constants.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A positive reference transport and a residual that vanishes linearly in
Wasserstein distance give one radius and one strictly positive margin. -/
theorem teacher_curvature_margin_exists (lambda kappa alpha Zo C : Real)
    (hlambda : 0 < lambda) (hkappa : 0 < kappa) (halpha : 0 < alpha)
    (hZo : 0 < Zo) (hC : 0 ≤ C) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧ ∀ Z D : Real, 0 ≤ D → D < rho →
      |Z-Zo| ≤ 4*Real.pi*D → 0 < Z ∧ c ≤ lambda*kappa*Z^alpha-C*D := by
  let K := lambda*kappa*(Zo/2)^alpha
  have hK : 0 < K := mul_pos (mul_pos hlambda hkappa) (Real.rpow_pos_of_pos (by linarith) _)
  let rho := min (Zo/(8*Real.pi)) (K/(2*(C+1)))
  have hrho : 0 < rho := lt_min (div_pos hZo (by positivity)) (div_pos hK (by positivity))
  refine ⟨rho,K/2,hrho,by positivity,?_⟩
  intro Z D hD hnear hclose
  have hD1 : D < Zo/(8*Real.pi) := hnear.trans_le (min_le_left _ _)
  have hD2 : D < K/(2*(C+1)) := hnear.trans_le (min_le_right _ _)
  have hclose' : 4*Real.pi*D < Zo/2 := by
    have hh := (lt_div_iff₀ (show 0 < 8*Real.pi by positivity)).mp hD1
    nlinarith
  have hZ : Zo/2 < Z := by
    have hh := (abs_le.mp hclose).1
    linarith
  have hres : C*D < K/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*(C+1) by positivity)).mp hD2
    nlinarith
  have hreg : K ≤ lambda*kappa*Z^alpha :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hZ.le halpha.le)
      (mul_pos hlambda hkappa).le
  exact ⟨lt_trans (by linarith) hZ, by linarith⟩

end PaperFormalization.MatrixFactorization
