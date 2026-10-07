import PaperFormalization.Manuscript.BoundedDifferenceProduct
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Bounded differences on an actual finite product probability space

Finite induction uses literal coordinate replacement and the exact product
integration step. Neither the moment-generating bound nor a tail inequality
is an assumption. The product measure, with possibly different factor laws,
is retained throughout.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal BigOperators

namespace PaperFormalization.Manuscript

variable {E : Type*} [MeasurableSpace E]

/-- Adjoining the first coordinate to the remaining genuine product has
exactly the finite product law. -/
theorem measurePreserving_finCons (n : ℕ) (μ : Fin (n + 1) → Measure E)
    [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (fun p : (Fin n → E) × E => Fin.cons p.2 p.1)
      ((Measure.pi fun i => μ i.succ).prod (μ 0)) (Measure.pi μ) := by
  have h := ((measurePreserving_piFinSuccAbove μ 0).symm).comp
    (Measure.measurePreserving_swap (μ := Measure.pi fun i : Fin n => μ i.succ) (ν := μ 0))
  simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using h

/-- McDiarmid's exact centered sub-Gaussian parameter, derived from actual
one-coordinate replacement bounds under a finite product probability law. -/
theorem hasSubgaussianMGF_centered_pi_of_bounded_differences (n : ℕ) :
    ∀ (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (Fin n → E) → ℝ) (M : ℝ≥0) (c : Fin n → ℝ≥0),
      Measurable f → (∀ x, |f x| ≤ M) →
      (∀ x i y, |f x - f (Function.update x i y)| ≤ c i) →
      HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂Measure.pi μ)
        (∑ i, (c i / 2) ^ 2) (Measure.pi μ) := by
  induction n with
  | zero =>
      intro μ hμ f M c hf hbound hchange
      have hconst (x : Fin 0 → E) : f x = f (fun i => Fin.elim0 i) :=
        congrArg f (Subsingleton.elim _ _)
      have hcenter : (fun x => f x - ∫ y, f y ∂Measure.pi μ) = fun _ => 0 := by
        funext x
        simp only [hconst, integral_const, probReal_univ, one_smul, sub_self]
      simpa only [hcenter, Fin.sum_univ_zero] using
        (HasSubgaussianMGF.fun_zero (μ := Measure.pi μ))
  | succ n ih =>
      intro μ hμ f M c hf hbound hchange
      let ν := Measure.pi (fun i : Fin n => μ i.succ)
      let F : (Fin n → E) × E → ℝ := fun p => f (Fin.cons p.2 p.1)
      let g : (Fin n → E) → ℝ := fun x => ∫ y, F (x,y) ∂μ 0
      have hpres := measurePreserving_finCons n μ
      have hF : Measurable F := hf.comp hpres.measurable
      have hFb (p : (Fin n → E) × E) : |F p| ≤ M := hbound _
      have hFi (x : Fin n → E) : Integrable (fun y => F (x,y)) (μ 0) :=
        Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
          M (Filter.Eventually.of_forall fun y => by
            simpa only [Real.norm_eq_abs] using hFb (x,y))
      have hg : Measurable g := hF.stronglyMeasurable.integral_prod_right'.measurable
      have hgb (x : Fin n → E) : |g x| ≤ M := by
        have hb := norm_integral_le_of_norm_le_const (μ := μ 0)
          (Filter.Eventually.of_forall fun y =>
            show ‖F (x,y)‖ ≤ (M : ℝ) by simpa only [Real.norm_eq_abs] using hFb (x,y))
        simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using hb
      have hgc (x : Fin n → E) (i : Fin n) (z : E) :
          |g x - g (Function.update x i z)| ≤ c i.succ := by
        dsimp only [g]
        rw [← integral_sub (hFi x) (hFi (Function.update x i z))]
        have hb := norm_integral_le_of_norm_le_const (μ := μ 0)
          (Filter.Eventually.of_forall fun y =>
            show ‖F (x,y) - F (Function.update x i z,y)‖ ≤ (c i.succ : ℝ) by
              simpa only [F, Fin.cons_update, Real.norm_eq_abs] using
                hchange (Fin.cons y x) i.succ z)
        simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using hb
      have hlast (x : Fin n → E) (y y' : E) : |F (x,y) - F (x,y')| ≤ c 0 := by
        simpa only [F, Fin.update_cons_zero] using hchange (Fin.cons y x) 0 y'
      have hmean := ih (fun i => μ i.succ) g M (fun i => c i.succ) hg hgb hgc
      have hprod := hasSubgaussianMGF_centered_prod_step ν (μ 0) F M (c 0)
        (∑ i : Fin n, (c i.succ / 2) ^ 2) hF hFb hlast hmean
      have hid : IdentDistrib F f (ν.prod (μ 0)) (Measure.pi μ) := by
        refine ⟨hF.aemeasurable, hf.aemeasurable, ?_⟩
        change Measure.map (f ∘ (fun p : (Fin n → E) × E => Fin.cons p.2 p.1))
          (ν.prod (μ 0)) = Measure.map f (Measure.pi μ)
        rw [← Measure.map_map hf hpres.measurable, hpres.map_eq]
      have hint := hid.integral_eq
      have hcenter := hid.comp (measurable_id.sub_const (∫ x, f x ∂Measure.pi μ))
      have hprod' : HasSubgaussianMGF
          (fun p => F p - ∫ x, f x ∂Measure.pi μ)
          ((∑ i : Fin n, (c i.succ / 2) ^ 2) + (c 0 / 2) ^ 2) (ν.prod (μ 0)) := by
        simpa only [hint] using hprod
      have hfinal := hprod'.congr_identDistrib hcenter
      simpa only [Function.comp_def, id_eq, Fin.sum_univ_succ, add_comm] using hfinal

/-- McDiarmid's one-sided upper tail with the exact exponent -2t²/Σcᵢ².
The zero-width case is valid here with totalized division; the following
lemma gives the stronger zero-probability statement at positive thresholds. -/
theorem measure_ge_le_of_pi_bounded_differences
    (n : ℕ) (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → E) → ℝ) (M : ℝ≥0) (c : Fin n → ℝ≥0)
    (hf : Measurable f) (hbound : ∀ x, |f x| ≤ M)
    (hchange : ∀ x i y, |f x - f (Function.update x i y)| ≤ c i)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ).real {x | (∫ y, f y ∂Measure.pi μ) + t ≤ f x} ≤
      exp (-2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  have hsg := hasSubgaussianMGF_centered_pi_of_bounded_differences n μ f M c
    hf hbound hchange
  have hp : ((∑ i, (c i / 2) ^ 2 : ℝ≥0) : ℝ) = (∑ i, (c i : ℝ) ^ 2) / 4 := by
    simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, Finset.sum_div]
  have he : -t ^ 2 / (2 * ((∑ i, (c i / 2) ^ 2 : ℝ≥0) : ℝ)) =
      -2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2 := by
    rw [hp, show 2 * ((∑ i, (c i : ℝ) ^ 2) / 4) = (∑ i, (c i : ℝ) ^ 2) / 2 by ring,
      div_div_eq_mul_div]
    ring
  have hset : {x | t ≤ f x - ∫ y, f y ∂Measure.pi μ} =
      {x | (∫ y, f y ∂Measure.pi μ) + t ≤ f x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  simpa only [hset, he] using hsg.measure_ge_le ht

/-- Zero sum of squared coordinate widths forces every positive centered
upper-deviation event to have zero probability under the same product law. -/
theorem measure_ge_eq_zero_of_pi_bounded_differences_zero
    (n : ℕ) (μ : Fin n → Measure E) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin n → E) → ℝ) (M : ℝ≥0) (c : Fin n → ℝ≥0)
    (hf : Measurable f) (hbound : ∀ x, |f x| ≤ M)
    (hchange : ∀ x i y, |f x - f (Function.update x i y)| ≤ c i)
    (hzero : ∑ i, (c i : ℝ) ^ 2 = 0) (t : ℝ) (ht : 0 < t) :
    (Measure.pi μ) {x | (∫ y, f y ∂Measure.pi μ) + t ≤ f x} = 0 := by
  have hsg := hasSubgaussianMGF_centered_pi_of_bounded_differences n μ f M c
    hf hbound hchange
  have hp : (∑ i, (c i / 2) ^ 2 : ℝ≥0) = 0 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_sum, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      NNReal.coe_zero, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, ← Finset.sum_div,
      hzero, zero_div]
  rw [hp] at hsg
  have hae := hsg.ae_eq_zero_of_hasSubgaussianMGF_zero
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hae] with x hx
  simp only [Pi.zero_apply] at hx
  linarith

end PaperFormalization.Manuscript
