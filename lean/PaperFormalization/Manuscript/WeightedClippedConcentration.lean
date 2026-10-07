import PaperFormalization.Manuscript.BoundedDifferenceFinite
import PaperFormalization.Manuscript.WeightedClippedSampleMean

/-! # Actual weighted clipped sample concentration

The amplitude is twice the original weighted clipped coordinate envelope.
Literal one-sample replacement therefore has width A/N, giving the exact
McDiarmid exponent -2Nt²/A². The centers remain integrals under the original
population law; neither the product law nor a sampled system is conditioned
on localization.
-/

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace PaperFormalization.Manuscript

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] {N : ℕ}

/-- The literal clipped statistic is nonnegative, uniformly bounded by the
actual source amplitude, and has exact one-coordinate width A/N. -/
theorem weightedClippedSampleResidual_bounded_differences (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n)))) :
    let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
    (∀ X : Fin N → E, 0 ≤ weightedClippedSampleResidual μ D w φ X ∧
      weightedClippedSampleResidual μ D w φ X ≤ A) ∧
    (∀ X : Fin N → E, ∀ i y,
      |weightedClippedSampleResidual μ D w φ X -
        weightedClippedSampleResidual μ D w φ (Function.update X i y)| ≤ A / N) := by
  classical
  let ψ : ∀ n, E → H n := fun n x => φ n (sourceRadialClip D x)
  let P : ∀ n, H n := fun n => ∫ x, ψ n x ∂μ
  let a : ℕ → ℝ := fun n => L n * (1 + D ^ m n)
  have hψ (n : ℕ) (x : E) : ‖ψ n x‖ ≤ a n :=
    norm_clipped_feature_le D (L n) (m n) hD (hL n) (φ n) (hgrowth n) x
  have hP (n : ℕ) : ‖P n‖ ≤ a n :=
    (clipped_populationFeature_integrable_and_norm_le μ D hD L m hL φ hc hgrowth n).2
  constructor
  · intro X
    refine ⟨tsum_nonneg (fun n => mul_nonneg (w n).coe_nonneg (norm_nonneg _)), ?_⟩
    exact weightedSampleResidual_le hN w ψ P a hsum hψ hP X
  · intro X i y
    exact weightedSampleResidual_one_sample_change_le hN w ψ P a hsum hψ hP
      X (Function.update X i y) i (fun j hji => (Function.update_of_ne hji y X).symm)

/-- Zero source amplitude forces the actual clipped statistic to vanish at
every configuration, before any probabilistic argument. -/
theorem weightedClippedSampleResidual_eq_zero_of_amplitude_zero (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n))))
    (hzero : 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n)) = 0)
    (X : Fin N → E) : weightedClippedSampleResidual μ D w φ X = 0 := by
  have hb := (weightedClippedSampleResidual_bounded_differences hN μ D hD w L m hL
    φ hc hgrowth hsum).1 X
  exact le_antisymm (hzero ▸ hb.2) hb.1

variable [∀ n, CompleteSpace (H n)]

/-- Actual product samples satisfy the exact mean bound A/(2sqrt N) and
centered McDiarmid tail exp(-2Nt²/A²), including zero amplitude. -/
theorem weightedClippedSampleResidual_pi_concentration (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (D : ℝ) (hD : 0 ≤ D)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n)))) :
    let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
    let f := (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ)
    let prodLaw := Measure.pi (fun _ : Fin N => μ)
    Integrable f prodLaw ∧ (∫ X, f X ∂prodLaw) ≤ A / (2 * sqrt N) ∧
      ∀ t : ℝ, 0 ≤ t → prodLaw.real {X | (∫ Y, f Y ∂prodLaw) + t ≤ f X} ≤
        exp (-2 * N * t ^ 2 / A ^ 2) := by
  let A : ℝ := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
  let f := (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ)
  let prodLaw := Measure.pi (fun _ : Fin N => μ)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (tsum_nonneg fun n => mul_nonneg (w n).coe_nonneg
      (mul_nonneg (hL n) (by positivity)))
  let ampNN : ℝ≥0 := .mk A hA
  have hf : Measurable f :=
    (continuous_measurable_weightedClippedSampleResidual hN μ D hD w L m hL φ hc hgrowth hsum).2
  have hb := weightedClippedSampleResidual_bounded_differences hN μ D hD w L m hL
    φ hc hgrowth hsum
  have hind : iIndepFun (fun i : Fin N => fun X : Fin N → E => X i) prodLaw :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have hexp := integrable_expected_weightedClippedSampleResidual_le hN μ prodLaw
    (fun i X => X i) (fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq)
    (fun _ _ hij => hind.indepFun hij) D hD w L m hL φ hc hgrowth hsum
  refine ⟨hexp.1, ?_, ?_⟩
  · calc
      _ ≤ (∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))) / sqrt N := hexp.2
      _ = A / (2 * sqrt N) := by dsimp only [A]; ring
  · intro t ht
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have htail := measure_ge_le_of_pi_bounded_differences N (fun _ => μ) f ampNN
      (fun _ => ampNN / N) hf
      (fun X => by rw [abs_of_nonneg (hb.1 X).1]; exact (hb.1 X).2)
      (fun X i y => by simpa only [NNReal.coe_div, NNReal.coe_natCast, ampNN, NNReal.coe_mk, A, f] using hb.2 X i y) t ht
    have hden : (∑ _i : Fin N, ((ampNN / N : ℝ≥0) : ℝ) ^ 2) = A ^ 2 / N := by
      simp only [NNReal.coe_div, NNReal.coe_natCast, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      change (N : ℝ) * (A / N) ^ 2 = A ^ 2 / N
      field_simp
    have he : -2 * t ^ 2 / (A ^ 2 / N) = -2 * N * t ^ 2 / A ^ 2 := by
      rw [div_div_eq_mul_div]
      ring
    simpa only [hden, he] using htail

/-- Fully independent original-system samples have the genuine product
configuration law. The same actual statistic has the exact mean and tail
bounds under that original law, with no localization reweighting. -/
theorem weightedClippedSampleResidual_iid_concentration
    {Ω : Type*} [MeasurableSpace Ω] (hN : 0 < N)
    (μ : Measure E) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Y : Fin N → Ω → E) (hLaw : ∀ i, ν.map (Y i) = μ)
    (hind : iIndepFun Y ν) (D : ℝ) (hD : 0 ≤ D)
    (w : ℕ → ℝ≥0) (L : ℕ → ℝ) (m : ℕ → ℕ) (hL : ∀ n, 0 ≤ L n)
    (φ : ∀ n, E → H n) (hc : ∀ n, Continuous (φ n))
    (hgrowth : ∀ n x, ‖φ n x‖ ≤ L n * (1 + ‖x‖ ^ m n))
    (hsum : Summable (fun n => (w n : ℝ) * (L n * (1 + D ^ m n)))) :
    let A := 2 * ∑' n, (w n : ℝ) * (L n * (1 + D ^ m n))
    let F := fun ω => weightedClippedSampleResidual μ D w φ (fun i => Y i ω)
    ν.map (fun ω i => Y i ω) = Measure.pi (fun _ : Fin N => μ) ∧
      Integrable F ν ∧ (∫ ω, F ω ∂ν) ≤ A / (2 * sqrt N) ∧
      ∀ t : ℝ, 0 ≤ t → ν.real {ω | (∫ z, F z ∂ν) + t ≤ F ω} ≤
        exp (-2 * N * t ^ 2 / A ^ 2) := by
  let f := (weightedClippedSampleResidual μ D w φ : (Fin N → E) → ℝ)
  let prodLaw := Measure.pi (fun _ : Fin N => μ)
  have hm (i : Fin N) : AEMeasurable (Y i) ν :=
    aemeasurable_of_map_neZero (by rw [hLaw i]; infer_instance)
  have hconfig : AEMeasurable (fun ω i => Y i ω) ν :=
    aemeasurable_pi_lambda (fun ω i => Y i ω) hm
  have hmap : ν.map (fun ω i => Y i ω) = prodLaw := by
    simpa only [hLaw] using hind.map_fun_eq_pi_map hm
  have hf : Measurable f :=
    (continuous_measurable_weightedClippedSampleResidual hN μ D hD w L m hL φ hc hgrowth hsum).2
  have hprod := weightedClippedSampleResidual_pi_concentration hN μ D hD w L m hL
    φ hc hgrowth hsum
  have hi : Integrable (fun ω => f (fun i => Y i ω)) ν := by
    have hi' : Integrable f (ν.map (fun ω i => Y i ω)) := hmap ▸ hprod.1
    exact hi'.comp_aemeasurable hconfig
  have hmean : (∫ ω, f (fun i => Y i ω) ∂ν) = ∫ X, f X ∂prodLaw := by
    rw [← hmap]
    exact (integral_map hconfig hf.aestronglyMeasurable).symm
  refine ⟨hmap, hi, ?_, ?_⟩
  · rw [hmean]
    exact hprod.2.1
  · intro t ht
    have hprob := map_measureReal_apply_of_aemeasurable hconfig
      (s := {X | (∫ Z, f Z ∂prodLaw) + t ≤ f X})
      (measurableSet_le measurable_const hf)
    rw [hmap] at hprob
    calc
      _ = prodLaw.real {X | (∫ Z, f Z ∂prodLaw) + t ≤ f X} := by
        rw [hmean]
        exact hprob.symm
      _ ≤ _ := hprod.2.2 t ht

end PaperFormalization.Manuscript
