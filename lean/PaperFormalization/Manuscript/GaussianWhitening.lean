import PaperFormalization.Manuscript.GaussianMatrixTail
import Mathlib.Probability.Independence.CharacteristicFunction

/-! # Gaussian whitening from exact generalized-inverse identities

The input population random vector is retained under its original measure.
The auxiliary standard Gaussian is genuinely independent. This module derives
the whitening law from exact algebraic identities; it does not construct the
generalized inverse or establish measurability as the matrices vary.
-/

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace PaperFormalization.Manuscript

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A continuous linear map transports the characteristic function by its
actual Hilbert adjoint. -/
theorem charFun_map_clm_adjoint (μ : Measure E) (A : E →L[ℝ] E) (x : E) :
    charFun (μ.map A) x = charFun μ (A.adjoint x) := by
  rw [charFun_eq_charFunDual_toDualMap, charFun_eq_charFunDual_toDualMap]
  change charFunDual (μ.map A) (innerSL ℝ x) = charFunDual μ (innerSL ℝ (A.adjoint x))
  rw [charFunDual_map, ContinuousLinearMap.innerSL_apply_comp]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A self-adjoint projection and its complement split the actual squared
Hilbert norm without any invertibility or rank restriction. -/
theorem projection_norm_sq_split (P : E →L[ℝ] E)
    (hP : P * P = P) (hself : P.adjoint = P) (x : E) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  have hPx : P (P x) = P x := congrArg (fun A : E →L[ℝ] E => A x) hP
  have hinner : inner ℝ x (P x) = ‖P x‖ ^ 2 := by
    calc
      _ = inner ℝ x (P.adjoint (P x)) := by rw [hself, hPx]
      _ = inner ℝ (P x) (P x) := ContinuousLinearMap.adjoint_inner_right P x (P x)
      _ = _ := real_inner_self_eq_norm_sq _
  change ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 = _
  rw [norm_sub_sq_real, hinner]
  ring

/-- Independent projected standard Gaussians in complementary orthogonal
subspaces sum to an actual standard Gaussian. -/
theorem complementary_gaussian_sum_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v h : Ω → E) (P : E →L[ℝ] E)
    (hP : P * P = P) (hself : P.adjoint = P)
    (hv : μ.map v = (stdGaussian E).map P)
    (hh : μ.map h = (stdGaussian E).map (1 - P : E →L[ℝ] E))
    (hind : IndepFun v h μ) :
    μ.map (fun ω => v ω + h ω) = stdGaussian E := by
  have hvm : AEMeasurable v μ := aemeasurable_of_map_neZero (by rw [hv]; infer_instance)
  have hhm : AEMeasurable h μ := aemeasurable_of_map_neZero (by rw [hh]; infer_instance)
  haveI : IsProbabilityMeasure (μ.map (fun ω => v ω + h ω)) :=
    Measure.isProbabilityMeasure_map (hvm.add hhm)
  apply Measure.ext_of_charFun
  funext x
  rw [hind.charFun_map_fun_add_eq_mul hvm hhm]
  simp only [Pi.mul_apply, hv, hh, charFun_map_clm_adjoint, charFun_stdGaussian,
    map_sub, ContinuousLinearMap.adjoint_one, hself]
  rw [← Complex.exp_add]
  congr 1
  have hsplit := projection_norm_sq_split P hP hself x
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hsplit
  push_cast at hc
  change (‖P x‖ : ℂ) ^ 2 + (‖(1 - P) x‖ : ℂ) ^ 2 = (‖x‖ : ℂ) ^ 2 at hc
  linear_combination -hc / 2

/-- The source whitening expression is standard Gaussian from a genuine
population Gaussian factor law and an independent auxiliary normal. The
projection identity is derived from BDB=B, not supplied as a result-law premise. -/
theorem gaussian_whitening_law
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (v h : Ω → E) (B D : E →L[ℝ] E)
    (hBDB : B * D * B = B) (hself : (D * B).adjoint = D * B)
    (hv : μ.map v = (stdGaussian E).map B) (hh : μ.map h = stdGaussian E)
    (hind : IndepFun v h μ) :
    μ.map (fun ω => D (v ω) + (1 - D * B) (h ω)) = stdGaussian E := by
  have hvm : AEMeasurable v μ := aemeasurable_of_map_neZero (by rw [hv]; infer_instance)
  have hhm : AEMeasurable h μ := aemeasurable_of_map_neZero (by rw [hh]; infer_instance)
  have hP : (D * B) * (D * B) = D * B := by
    calc
      _ = D * (B * D * B) := by noncomm_ring
      _ = _ := by rw [hBDB]
  have hvD : μ.map (fun ω => D (v ω)) = (stdGaussian E).map (D * B) := by
    change μ.map (D ∘ v) = _
    rw [← AEMeasurable.map_map_of_aemeasurable D.continuous.aemeasurable hvm, hv,
      Measure.map_map D.continuous.measurable B.continuous.measurable]
    rfl
  have hhP : μ.map (fun ω => (1 - D * B) (h ω)) = (stdGaussian E).map (1 - D * B : E →L[ℝ] E) := by
    change μ.map (((1 - D * B : E →L[ℝ] E) : E → E) ∘ h) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (1 - D * B).continuous.aemeasurable hhm, hh]
  exact complementary_gaussian_sum_law μ _ _ (D * B) hP hself hvD hhP
    (hind.comp D.continuous.measurable (1 - D * B).continuous.measurable)

/-- Multiplying the whitening expression by B retains the original population
random vector almost surely, including singular and zero factors. -/
theorem gaussian_whitening_reproduces_population
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (v h : Ω → E) (B D : E →L[ℝ] E)
    (hBDB : B * D * B = B) (hv : μ.map v = (stdGaussian E).map B) :
    ∀ᵐ ω ∂μ, B (D (v ω) + (1 - D * B) (h ω)) = v ω := by
  have hvm : AEMeasurable v μ := aemeasurable_of_map_neZero (by rw [hv]; infer_instance)
  have hpop : ∀ᵐ x ∂(stdGaussian E).map B, B (D x) = x := by
    apply (ae_map_iff B.continuous.aemeasurable (by measurability)).mpr
    exact Filter.Eventually.of_forall (fun x => congrArg (fun A : E →L[ℝ] E => A x) hBDB)
  have hretain : ∀ᵐ ω ∂μ, B (D (v ω)) = v ω :=
    ae_of_ae_map (p := fun x => B (D x) = x) hvm (by rw [hv]; exact hpop)
  filter_upwards [hretain] with ω hω
  have hb : B (D (B (h ω))) = B (h ω) := congrArg (fun A : E →L[ℝ] E => A (h ω)) hBDB
  change B (D (v ω) + (h ω - D (B (h ω)))) = v ω
  rw [map_add, map_sub, hω, hb, sub_self, add_zero]

end Hilbert

end PaperFormalization.Manuscript
