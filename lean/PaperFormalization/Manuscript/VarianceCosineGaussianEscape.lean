import PaperFormalization.Manuscript.VarianceCosineEscapeGeometry
import PaperFormalization.Manuscript.VarianceCosineCoupling
import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Gaussian avoidance of the even-integer lattice
M13v VERIFIED UNIT (full example application remains open). Countable interval estimates use ENNReal integrals; no
integrability is inferred from a totalized real integral. A slightly larger
fixed constant than the manuscript's displayed constant avoids needing a
half-line Gaussian mass identity. The probability exponent is unchanged.
-/
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal
namespace PaperFormalization.Manuscript

/-- The centered Gaussian density decreases with absolute distance. -/
theorem varianceCosineGaussian_pdf_mono (v : NNReal) (x y : Real)
    (hxy : abs x <= abs y) : gaussianPDFReal 0 v y <= gaussianPDFReal 0 v x := by
  have hs : x^2 <= y^2 := (sq_le_sq).mpr hxy
  unfold gaussianPDFReal
  simp only [sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (neg_le_neg hs) (by positivity)

/-- A density upper bound on an interval, including an empty interval. -/
theorem varianceCosineGaussian_interval_upper (v : NNReal) (hv : v ≠ 0)
    (A B d : Real) (hd : 0 <= d)
    (h : forall x, x ∈ Ioo A B -> d <= abs x) :
    gaussianReal 0 v (Ioo A B) <=
      ENNReal.ofReal (B-A) * ENNReal.ofReal (gaussianPDFReal 0 v d) := by
  rw [gaussianReal_apply 0 hv]
  calc
    _ <= ∫⁻ x in Ioo A B, ENNReal.ofReal (gaussianPDFReal 0 v d) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ENNReal.ofReal_le_ofReal (varianceCosineGaussian_pdf_mono v d x
        (by simpa only [abs_of_nonneg hd] using h x hx))
    _ = _ := by simp [Real.volume_Ioo,mul_comm]

/-- The reverse comparison on a unit reference interval. -/
theorem varianceCosineGaussian_interval_lower (v : NNReal) (hv : v ≠ 0)
    (A B d : Real) (hd : 0 <= d)
    (h : forall x, x ∈ Ioo A B -> abs x <= d) :
    ENNReal.ofReal (B-A) * ENNReal.ofReal (gaussianPDFReal 0 v d) <=
      gaussianReal 0 v (Ioo A B) := by
  rw [gaussianReal_apply 0 hv]
  calc
    _ = ∫⁻ x in Ioo A B, ENNReal.ofReal (gaussianPDFReal 0 v d) := by
      simp [Real.volume_Ioo,mul_comm]
    _ <= _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact ENNReal.ofReal_le_ofReal (varianceCosineGaussian_pdf_mono v x d
        (by simpa only [abs_of_nonneg hd] using h x hx))

def varianceCosinePositiveLanding (rho : Real) (k : Nat) : Set Real :=
  Ioo (2*((k:Real)+1)-rho) (2*((k:Real)+1)+rho)
def varianceCosineNegativeLanding (rho : Real) (k : Nat) : Set Real :=
  Ioo (-2*((k:Real)+1)-rho) (-2*((k:Real)+1)+rho)
def varianceCosinePositiveReference (k : Nat) : Set Real := Ioo (2*(k:Real)) (2*(k:Real)+1)
def varianceCosineNegativeReference (k : Nat) : Set Real := Ioo (-(2*(k:Real)+1)) (-2*(k:Real))

theorem varianceCosineGaussian_positive_interval (v : NNReal) (hv : v ≠ 0)
    (rho : Real) (hr : 0 <= rho) (hr1 : rho <= 1) (k : Nat) :
    gaussianReal 0 v (varianceCosinePositiveLanding rho k) <=
      ENNReal.ofReal (2*rho) * gaussianReal 0 v (varianceCosinePositiveReference k) := by
  have hk : 0 <= (k:Real) := Nat.cast_nonneg k
  have hu := varianceCosineGaussian_interval_upper v hv
    (2*((k:Real)+1)-rho) (2*((k:Real)+1)+rho) (2*(k:Real)+1) (by positivity)
    (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1] : 0 <= x)]; linarith [hx.1])
  have hl := varianceCosineGaussian_interval_lower v hv
    (2*(k:Real)) (2*(k:Real)+1) (2*(k:Real)+1) (by positivity)
    (fun x hx => by rw [abs_of_nonneg (by linarith [hx.1] : 0 <= x)]; exact hx.2.le)
  have hlen : (2*((k:Real)+1)+rho)-(2*((k:Real)+1)-rho)=2*rho := by ring
  rw [hlen] at hu
  have hunit : (2*(k:Real)+1)-2*(k:Real)=1 := by ring
  rw [hunit,ENNReal.ofReal_one,one_mul] at hl
  exact hu.trans (mul_le_mul_left' hl _)

theorem varianceCosineGaussian_negative_interval (v : NNReal) (hv : v ≠ 0)
    (rho : Real) (hr : 0 <= rho) (hr1 : rho <= 1) (k : Nat) :
    gaussianReal 0 v (varianceCosineNegativeLanding rho k) <=
      ENNReal.ofReal (2*rho) * gaussianReal 0 v (varianceCosineNegativeReference k) := by
  have hk : 0 <= (k:Real) := Nat.cast_nonneg k
  have hu := varianceCosineGaussian_interval_upper v hv
    (-2*((k:Real)+1)-rho) (-2*((k:Real)+1)+rho) (2*(k:Real)+1) (by positivity)
    (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2] : x <= 0)]; linarith [hx.2])
  have hl := varianceCosineGaussian_interval_lower v hv
    (-(2*(k:Real)+1)) (-2*(k:Real)) (2*(k:Real)+1) (by positivity)
    (fun x hx => by rw [abs_of_nonpos (by linarith [hx.2] : x <= 0)]; linarith [hx.1])
  have hlen : (-2*((k:Real)+1)+rho)-(-2*((k:Real)+1)-rho)=2*rho := by ring
  rw [hlen] at hu
  have hunit : -2*(k:Real)-(-(2*(k:Real)+1))=1 := by ring
  rw [hunit,ENNReal.ofReal_one,one_mul] at hl
  exact hu.trans (mul_le_mul_left' hl _)

theorem varianceCosinePositiveReference_disjoint :
    Pairwise (Disjoint on varianceCosinePositiveReference) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  . have hc : (i:Real)+1 <= j := by exact_mod_cast (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (by linarith [hj.1] : 2*(i:Real)+1 <= x)) hi.2
  . have hc : (j:Real)+1 <= i := by exact_mod_cast (Nat.succ_le_of_lt h)
    exact (not_lt_of_ge (by linarith [hi.1] : 2*(j:Real)+1 <= x)) hj.2

theorem varianceCosineNegativeReference_disjoint :
    Pairwise (Disjoint on varianceCosineNegativeReference) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  . have hc : (i:Real)+1 <= j := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hi.1,hj.2]
  . have hc : (j:Real)+1 <= i := by exact_mod_cast (Nat.succ_le_of_lt h)
    linarith [hj.1,hi.2]

/-- A countable family dominated by disjoint reference masses. -/
theorem varianceCosine_union_of_disjoint_dominators
    (mu : Measure Real) [IsProbabilityMeasure mu]
    (A B : Nat -> Set Real) (hB : forall k, MeasurableSet (B k))
    (hd : Pairwise (Disjoint on B)) (c : ENNReal)
    (h : forall k, mu (A k) <= c*mu (B k)) : mu (⋃ k, A k) <= c := by
  calc
    _ <= ∑' k, mu (A k) := measure_iUnion_le _
    _ <= ∑' k, c*mu (B k) := ENNReal.tsum_le_tsum h
    _ = c*(∑' k, mu (B k)) := ENNReal.tsum_mul_left
    _ = c*mu (⋃ k, B k) := by rw [measure_iUnion hd hB]
    _ <= c*1 := mul_le_mul_left' prob_le_one c
    _ = c := mul_one _

/-- Splitting all integer centers into zero, positive and negative centers. -/
theorem varianceCosineEscapeLanding_bad_cover (rho : Real) :
    {x | ¬ varianceCosineEscapeLanding rho x} ⊆
      (Ioo (-rho) rho ∪ (⋃ k, varianceCosinePositiveLanding rho k)) ∪
        (⋃ k, varianceCosineNegativeLanding rho k) := by
  intro x hx
  simp only [varianceCosineEscapeLanding,not_forall,not_le] at hx
  obtain ⟨k,hk⟩ := hx
  rcases k with k | k
  . cases k with
    | zero =>
      exact Or.inl (Or.inl (by simpa using abs_lt.mp hk))
    | succ k =>
      apply Or.inl; apply Or.inr; apply Set.mem_iUnion.mpr; refine ⟨k,?_⟩
      have hh := abs_lt.mp hk
      change x ∈ Ioo _ _
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_add, Int.cast_one, Nat.cast_add, Nat.cast_one] at hh
      constructor <;> linarith [hh.1,hh.2]
  . apply Or.inr; apply Set.mem_iUnion.mpr; refine ⟨k,?_⟩
    have hh := abs_lt.mp hk
    change x ∈ Ioo _ _
    push_cast at hh
    constructor <;> linarith [hh.1,hh.2]

noncomputable def varianceCosineEscapeConstant (v : NNReal) : Real :=
  2*gaussianPDFReal 0 v 0+4

theorem varianceCosineEscapeConstant_ge_four (v : NNReal) :
    4 <= varianceCosineEscapeConstant v := by
  unfold varianceCosineEscapeConstant
  linarith [gaussianPDFReal_nonneg 0 v 0]

/-- Gaussian anti-concentration at every even integer, with a constant
independent of the number of particles and of the time horizon. -/
theorem varianceCosineGaussian_escape_failure (v : NNReal) (hv : v ≠ 0)
    (rho : Real) (hr : 0 <= rho) (hr1 : rho <= 1) :
    gaussianReal 0 v {x | ¬ varianceCosineEscapeLanding rho x} <=
      ENNReal.ofReal (varianceCosineEscapeConstant v*rho) := by
  have h0 := varianceCosineGaussian_interval_upper v hv (-rho) rho 0 le_rfl
    (fun x _ => abs_nonneg x)
  rw [sub_neg_eq_add,show rho+rho=2*rho by ring] at h0
  have hp := varianceCosine_union_of_disjoint_dominators (gaussianReal 0 v)
    (varianceCosinePositiveLanding rho) varianceCosinePositiveReference
    (fun _ => measurableSet_Ioo) varianceCosinePositiveReference_disjoint _
    (varianceCosineGaussian_positive_interval v hv rho hr hr1)
  have hn := varianceCosine_union_of_disjoint_dominators (gaussianReal 0 v)
    (varianceCosineNegativeLanding rho) varianceCosineNegativeReference
    (fun _ => measurableSet_Ioo) varianceCosineNegativeReference_disjoint _
    (varianceCosineGaussian_negative_interval v hv rho hr hr1)
  calc
    _ <= gaussianReal 0 v ((Ioo (-rho) rho ∪ (⋃ k, varianceCosinePositiveLanding rho k)) ∪
      (⋃ k, varianceCosineNegativeLanding rho k)) := measure_mono (varianceCosineEscapeLanding_bad_cover rho)
    _ <= (gaussianReal 0 v (Ioo (-rho) rho)+
      gaussianReal 0 v (⋃ k, varianceCosinePositiveLanding rho k))+
      gaussianReal 0 v (⋃ k, varianceCosineNegativeLanding rho k) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ <= (ENNReal.ofReal (2*rho)*ENNReal.ofReal (gaussianPDFReal 0 v 0)+
      ENNReal.ofReal (2*rho))+ENNReal.ofReal (2*rho) := add_le_add (add_le_add h0 hp) hn
    _ = _ := by
      have hf := gaussianPDFReal_nonneg 0 v 0
      rw [<- ENNReal.ofReal_mul (by positivity),
        <- ENNReal.ofReal_add (by positivity) (by positivity),
        <- ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold varianceCosineEscapeConstant
      ring

noncomputable def varianceCosineEscapeRadius (v : NNReal) (p : Real) : Real :=
  p/(2*varianceCosineEscapeConstant v)

theorem varianceCosineEscapeRadius_bounds (v : NNReal) (p : Real)
    (hp : 0 < p) (hp1 : p <= 1) :
    0 < varianceCosineEscapeRadius v p ∧ varianceCosineEscapeRadius v p <= 1/8 := by
  have hc := varianceCosineEscapeConstant_ge_four v
  unfold varianceCosineEscapeRadius
  constructor
  . positivity
  . apply (div_le_iff₀ (by linarith : 0 < 2*varianceCosineEscapeConstant v)).mpr
    linarith

theorem varianceCosineGaussian_escape_budget (v : NNReal) (hv : v ≠ 0)
    (p : Real) (hp : 0 < p) (hp1 : p <= 1) :
    gaussianReal 0 v {x | ¬ varianceCosineEscapeLanding (varianceCosineEscapeRadius v p) x} <=
      ENNReal.ofReal (p/2) := by
  have hr := varianceCosineEscapeRadius_bounds v p hp hp1
  have h := varianceCosineGaussian_escape_failure v hv _ hr.1.le (by linarith [hr.2])
  have hc : varianceCosineEscapeConstant v ≠ 0 := by linarith [varianceCosineEscapeConstant_ge_four v]
  have he : varianceCosineEscapeConstant v*varianceCosineEscapeRadius v p=p/2 := by
    unfold varianceCosineEscapeRadius
    field_simp <;> ring
  rwa [he] at h

/-- The event only reads the original population scalar; no seed or initial
sample occurs here. The original joint law is not conditioned or replaced. -/
def varianceCosineEscapeEvent {N : Nat} (sigma rho : Real) : Set (VarianceCosineCouplingSpace N) :=
  {w | varianceCosineEscapeLanding rho (-sigma*w.2.1)}

theorem varianceCosineEscapeEvent_measurable {N : Nat} (sigma rho : Real) :
    MeasurableSet (varianceCosineEscapeEvent (N := N) sigma rho) :=
  (varianceCosineEscapeLanding_measurable rho).preimage (by fun_prop)

/-- The actual population-first extension retains the full Gaussian landing
law. The auxiliary seed and Z need not be independent. -/
theorem varianceCosineCoupling_landing_law {N : Nat}
    (mu : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure mu] (sigma : Real) :
    (varianceCosineCouplingLaw mu).map (fun w => -sigma*w.2.1) =
      gaussianReal 0 (⟨sigma^2,sq_nonneg sigma⟩ : NNReal) := by
  have hZ : (varianceCosineCouplingLaw mu).map (fun w => w.2.1) = gaussianReal 0 1 := by
    exact (measurePreserving_fst.comp (measurePreserving_snd : MeasurePreserving
      (Prod.snd : VarianceCosineCouplingSpace N -> Real × SourceStepNormal N 1)
      (varianceCosineCouplingLaw mu) ((gaussianReal 0 1).prod (stdGaussian _)))).map_eq
  rw [show (fun w : VarianceCosineCouplingSpace N => -sigma*w.2.1) =
    (fun x : Real => -sigma*x) ∘ (fun w => w.2.1) by rfl,
    <- Measure.map_map (by fun_prop) (by fun_prop),hZ,gaussianReal_map_const_mul]
  simp
  rfl

theorem varianceCosineEscapeEvent_budget {N : Nat}
    (mu : Measure (SourceFiniteConfiguration N 1)) [IsProbabilityMeasure mu]
    (sigma p : Real) (hs : 0 < sigma) (hp : 0 < p) (hp1 : p <= 1) :
    let v : NNReal := ⟨sigma^2,sq_nonneg sigma⟩
    (varianceCosineCouplingLaw mu) (varianceCosineEscapeEvent sigma (varianceCosineEscapeRadius v p))ᶜ <=
      ENNReal.ofReal (p/2) := by
  let v : NNReal := ⟨sigma^2,sq_nonneg sigma⟩
  have hv : v ≠ 0 := by intro h; have hh := congrArg (fun v : NNReal => (v:Real)) h; change sigma^2 = 0 at hh; nlinarith
  have hl := varianceCosineCoupling_landing_law mu sigma
  have hm := (varianceCosineEscapeLanding_measurable (varianceCosineEscapeRadius v p)).compl
  change MeasurableSet {x | ¬ varianceCosineEscapeLanding (varianceCosineEscapeRadius v p) x} at hm
  have hmap := Measure.map_apply (μ := varianceCosineCouplingLaw mu) (by fun_prop : Measurable (fun w : VarianceCosineCouplingSpace N => -sigma*w.2.1)) hm
  change (varianceCosineCouplingLaw mu) ((fun w => -sigma*w.2.1) ⁻¹' {x | ¬ varianceCosineEscapeLanding (varianceCosineEscapeRadius v p) x}) <= _
  rw [<- hmap,hl]
  exact varianceCosineGaussian_escape_budget v hv p hp hp1
end PaperFormalization.Manuscript
