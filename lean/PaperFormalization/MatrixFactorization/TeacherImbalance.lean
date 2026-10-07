import PaperFormalization.MatrixFactorization.TransverseFeatureSignal

/-! # Two-sided sliced teacher imbalance

The hypothesis below retains positivity on every Borel latitude set. It does
not require the transverse projection to be nonnegative at each teacher point.
The scalar integration lemma proves the needed implication by comparing the
pushforwards of the positive and negative density parts.
-/

open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def twoSidedLatitude {d : Nat} (pole w : UnitSphere d) : Real :=
  |inner Real pole.val w.val|

noncomputable def teacherTransverseProjection {d : Nat} (pole w : UnitSphere d) : Weight d :=
  w.val - (inner Real pole.val w.val) • pole.val

theorem twoSidedLatitude_continuous {d : Nat} (pole : UnitSphere d) :
    Continuous (twoSidedLatitude pole) := by unfold twoSidedLatitude; fun_prop

theorem twoSidedLatitude_mem {d : Nat} (pole w : UnitSphere d) :
    twoSidedLatitude pole w ∈ Icc (0 : Real) 1 := by
  have hp : ‖pole.val‖ = 1 := by simpa using pole.property
  have hw : ‖w.val‖ = 1 := by simpa using w.property
  exact ⟨abs_nonneg _, by simpa [twoSidedLatitude, hp, hw] using
    abs_real_inner_le_norm pole.val w.val⟩

theorem teacherTransverseProjection_continuous {d : Nat} (pole : UnitSphere d) :
    Continuous (teacherTransverseProjection pole) := by unfold teacherTransverseProjection; fun_prop

theorem teacherTransverseProjection_tangent {d : Nat} (pole w : UnitSphere d) :
    inner Real pole.val (teacherTransverseProjection pole w) = 0 := by
  have hp : ‖pole.val‖ = 1 := by simpa using pole.property
  simp [teacherTransverseProjection, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hp]

noncomputable def slicedTransverseMoment {d : Nat} (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) (E : Set Real) : Weight d :=
  ∫ w in (twoSidedLatitude pole) ⁻¹' E, teacherTransverseProjection pole w ∂teacher

theorem slicedTransverseMoment_pairing {d : Nat} (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] (e : Weight d) (E : Set Real) :
    inner Real e (slicedTransverseMoment pole teacher E) =
      ∫ w in (twoSidedLatitude pole) ⁻¹' E,
        inner Real e (teacherTransverseProjection pole w) ∂teacher := by
  unfold slicedTransverseMoment
  exact (integral_inner (sphere_integrable teacher _
    (teacherTransverseProjection_continuous pole)).integrableOn e).symm

/-- The source assumption, including a unit tangent witness and strict visible
latitude mass. Positivity is imposed on slices rather than on individual points. -/
structure TwoSidedTeacherImbalance {d : Nat} (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) (e : Weight d) (rvis gamma : Real) : Prop where
  unit : ‖e‖ = 1
  tangent : inner Real pole.val e = 0
  radius_pos : 0 < rvis
  radius_lt_one : rvis < 1
  margin_pos : 0 < gamma
  slices_nonneg : ∀ E : Set Real, MeasurableSet E → E ⊆ Icc (0 : Real) 1 →
    0 ≤ inner Real e (slicedTransverseMoment pole teacher E)
  visible_lower : gamma ≤ inner Real e
    (slicedTransverseMoment pole teacher (Icc rvis 1))

theorem TwoSidedTeacherImbalance.all_slices_nonneg {d : Nat} {pole : UnitSphere d}
    {teacher : Measure (UnitSphere d)} [IsFiniteMeasure teacher] {e : Weight d}
    {rvis gamma : Real} (h : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (E : Set Real) (hE : MeasurableSet E) :
    0 ≤ ∫ w in (twoSidedLatitude pole) ⁻¹' E,
      inner Real e (teacherTransverseProjection pole w) ∂teacher := by
  have he : (twoSidedLatitude pole) ⁻¹' (E ∩ Icc (0 : Real) 1) =
      (twoSidedLatitude pole) ⁻¹' E := by
    ext w
    simp only [mem_preimage, mem_inter_iff, and_iff_left_iff_imp]
    exact fun _ => twoSidedLatitude_mem pole w
  have hn := h.slices_nonneg (E ∩ Icc 0 1) (hE.inter measurableSet_Icc) inter_subset_right
  rw [slicedTransverseMoment_pairing, he] at hn
  exact hn

/-- Positivity on all measurable slices implies positivity against any
nonnegative measurable weight for which the two density products are integrable. -/
theorem integral_weight_nonneg_of_slices {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (mu : Measure α) (r : α → β) (g : α → Real)
    (hr : Measurable r) (hg : Measurable g) (hgi : Integrable g mu)
    (hslices : ∀ E : Set β, MeasurableSet E → 0 ≤ ∫ x in r ⁻¹' E, g x ∂mu)
    (psi : β → Real) (hpsi : Measurable psi) (hpos : ∀ y, 0 ≤ psi y)
    (hip : Integrable (fun x => max (g x) 0 * psi (r x)) mu)
    (hin : Integrable (fun x => max (-g x) 0 * psi (r x)) mu) :
    0 ≤ ∫ x, psi (r x) * g x ∂mu := by
  let mup := mu.withDensity (fun x => ENNReal.ofReal (g x))
  let mun := mu.withDensity (fun x => ENNReal.ofReal (-g x))
  have hpint : Integrable (fun x => max (g x) 0) mu := hgi.pos_part
  have hnint : Integrable (fun x => max (-g x) 0) mu := hgi.neg_part
  have hle : Measure.map r mun ≤ Measure.map r mup := by
    apply Measure.le_iff.mpr
    intro E hE
    rw [Measure.map_apply hr hE, Measure.map_apply hr hE]
    simp only [mun, mup, withDensity_apply _ (hr hE)]
    have hp := ofReal_integral_eq_lintegral_ofReal (hpint.integrableOn (s := r ⁻¹' E))
      (Filter.Eventually.of_forall (fun x => le_max_right (g x) 0))
    have hn := ofReal_integral_eq_lintegral_ofReal (hnint.integrableOn (s := r ⁻¹' E))
      (Filter.Eventually.of_forall (fun x => le_max_right (-g x) 0))
    simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show (0 : ENNReal) ≤ _ from zero_le)] at hp hn
    rw [← hp, ← hn]
    apply ENNReal.ofReal_le_ofReal
    have he : (fun x => g x) = (fun x => max (g x) 0 - max (-g x) 0) := by
      funext x; exact (max_zero_sub_max_neg_zero_eq_self (g x)).symm
    have hn := hslices E hE
    rw [he, integral_sub hpint.integrableOn hnint.integrableOn] at hn
    linarith
  have hpi : Integrable psi (Measure.map r mup) := by
    rw [integrable_map_measure hpsi.aestronglyMeasurable hr.aemeasurable]
    apply (integrable_withDensity_iff_integrable_smul' hg.ennreal_ofReal
      (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))).mpr
    simpa [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_def] using hip
  have hpull (g' : α → Real) (hg' : Measurable g') :
      (∫ y, psi y ∂Measure.map r (mu.withDensity (fun x => ENNReal.ofReal (g' x)))) =
      ∫ x, max (g' x) 0 * psi (r x) ∂mu := by
    rw [integral_map hr.aemeasurable hpsi.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hg'.ennreal_ofReal
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  have hn := integral_mono_measure hle (Filter.Eventually.of_forall hpos) hpi
  change (∫ y, psi y ∂Measure.map r (mu.withDensity (fun x => ENNReal.ofReal (-g x)))) ≤
    (∫ y, psi y ∂Measure.map r (mu.withDensity (fun x => ENNReal.ofReal (g x)))) at hn
  rw [hpull g hg, hpull (fun x => -g x) hg.neg] at hn
  have he : (fun x => psi (r x) * g x) =
      (fun x => max (g x) 0 * psi (r x) - max (-g x) 0 * psi (r x)) := by
    funext x
    rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self, mul_comm]
  rw [he, integral_sub hip hin]
  linarith

end PaperFormalization.MatrixFactorization
