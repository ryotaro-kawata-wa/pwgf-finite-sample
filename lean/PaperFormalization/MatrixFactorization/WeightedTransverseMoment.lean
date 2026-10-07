import PaperFormalization.MatrixFactorization.TeacherImbalance

/-! # The original active-weighted transverse teacher moment

The finite active weight keeps the source factor `n / 2` and uses the original
teacher measure. Its monotonicity identifies the source interval infimum with
the left-endpoint value; no compactness-derived lower bound is substituted.
-/

open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def activeLatitudeWeight {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (r : Real) : Real :=
  (1/2 : Real) * ∑ n ∈ O, (n : Real) * ‖a n‖^2 * r^(n-1)

theorem activeLatitudeWeight_continuous {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) : Continuous (activeLatitudeWeight O a) := by
  unfold activeLatitudeWeight
  fun_prop

theorem activeLatitudeWeight_nonneg {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) {r : Real} (hr : 0 ≤ r) : 0 ≤ activeLatitudeWeight O a r := by
  unfold activeLatitudeWeight
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg n)
    (sq_nonneg _)) (pow_nonneg hr _))

theorem activeLatitudeWeight_monotoneOn {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) : MonotoneOn (activeLatitudeWeight O a) (Ici (0 : Real)) := by
  intro r hr s hs hrs
  unfold activeLatitudeWeight
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hr hrs _) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)))

theorem activeLatitudeWeight_pos {h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (hactive : ∃ n ∈ O, a n ≠ 0)
    {r : Real} (hr : 0 < r) : 0 < activeLatitudeWeight O a r := by
  obtain ⟨n, hn, ha⟩ := hactive
  unfold activeLatitudeWeight
  apply mul_pos (by norm_num)
  apply Finset.sum_pos' (fun m _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)) (pow_nonneg hr.le _))
  refine ⟨n, hn, mul_pos (mul_pos ?_ (sq_pos_of_pos (norm_pos_iff.mpr ha))) (pow_pos hr _)⟩
  exact_mod_cast (hO n hn).pos

noncomputable def activeLatitudeMinimum {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (rvis : Real) : Real :=
  sInf (activeLatitudeWeight O a '' Icc rvis 1)

theorem activeLatitudeMinimum_eq {h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    {rvis : Real} (hr : 0 ≤ rvis) (hr1 : rvis ≤ 1) :
    activeLatitudeMinimum O a rvis = activeLatitudeWeight O a rvis := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨_, ⟨rvis, ⟨le_rfl, hr1⟩, rfl⟩⟩
  · intro x hx
    obtain ⟨r, hrr, rfl⟩ := hx
    exact activeLatitudeWeight_monotoneOn O a hr (hr.trans hrr.1) hrr.1
  · intro b hb
    exact ⟨_, ⟨rvis, ⟨le_rfl, hr1⟩, rfl⟩, hb⟩

theorem activeLatitudeMinimum_pos {h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hO : ∀ n, n ∈ O → Odd n) (hactive : ∃ n ∈ O, a n ≠ 0)
    {rvis : Real} (hr : 0 < rvis) (hr1 : rvis ≤ 1) :
    0 < activeLatitudeMinimum O a rvis := by
  rw [activeLatitudeMinimum_eq O a hr.le hr1]
  exact activeLatitudeWeight_pos O a hO hactive hr

noncomputable def weightedTransverseMoment {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) : Weight d :=
  ∫ w, activeLatitudeWeight O a (twoSidedLatitude pole w) • teacherTransverseProjection pole w ∂teacher

theorem weightedTransverseMoment_integrable {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] :
    Integrable (fun w => activeLatitudeWeight O a (twoSidedLatitude pole w) •
      teacherTransverseProjection pole w) teacher := by
  apply sphere_integrable
  exact ((activeLatitudeWeight_continuous O a).comp (twoSidedLatitude_continuous pole)).smul
    (teacherTransverseProjection_continuous pole)

theorem weightedTransverseMoment_pairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (e : Weight d) :
    inner Real e (weightedTransverseMoment O a pole teacher) =
      ∫ w, activeLatitudeWeight O a (twoSidedLatitude pole w) *
        inner Real e (teacherTransverseProjection pole w) ∂teacher := by
  rw [weightedTransverseMoment, ← integral_inner (weightedTransverseMoment_integrable O a pole teacher)]
  simp only [real_inner_smul_right]

theorem weightedTransverseMoment_tangent {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] : inner Real pole.val (weightedTransverseMoment O a pole teacher) = 0 := by
  rw [weightedTransverseMoment_pairing]
  simp only [teacherTransverseProjection_tangent, mul_zero, integral_zero]

/-- The quantitative lower bound follows from sliced positivity alone. The
auxiliary residual weight is nonnegative on every latitude, including those
below the visible band; the teacher projection itself may have either sign. -/
theorem weightedTransverseMoment_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    activeLatitudeMinimum O a rvis * gamma ≤
      inner Real e (weightedTransverseMoment O a pole teacher) := by
  classical
  let k := activeLatitudeWeight O a
  let r := twoSidedLatitude pole
  let g := fun w : UnitSphere d => inner Real e (teacherTransverseProjection pole w)
  let psi := fun x : Real => k (max x 0) - (Ici rvis).indicator (fun _ => k rvis) x
  have hk : Continuous k := activeLatitudeWeight_continuous O a
  have hr : Continuous r := twoSidedLatitude_continuous pole
  have hg : Continuous g := continuous_const.inner (teacherTransverseProjection_continuous pole)
  have hki : 0 ≤ k rvis := activeLatitudeWeight_nonneg O a himb.radius_pos.le
  have hpsim : Measurable psi :=
    (hk.measurable.comp (measurable_id.max measurable_const)).sub
      (measurable_const.indicator measurableSet_Ici)
  have hpsip (x : Real) : 0 ≤ psi x := by
    dsimp [psi]
    by_cases hx : rvis ≤ x
    · rw [indicator_of_mem (s := Ici rvis) hx, max_eq_left (himb.radius_pos.le.trans hx)]
      exact sub_nonneg.mpr (activeLatitudeWeight_monotoneOn O a
        himb.radius_pos.le (himb.radius_pos.le.trans hx) hx)
    · rw [indicator_of_notMem (s := Ici rvis) hx, sub_zero]
      exact activeLatitudeWeight_nonneg O a (le_max_right _ _)
  have hpsib (w : UnitSphere d) : ‖psi (r w)‖ ≤ k 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpsip _)]
    have hmem := twoSidedLatitude_mem pole w
    have hk1 : k (r w) ≤ k 1 := activeLatitudeWeight_monotoneOn O a hmem.1 (by norm_num) hmem.2
    have hi : 0 ≤ (Ici rvis).indicator (fun _ => k rvis) (r w) :=
      indicator_nonneg (fun _ _ => hki) _
    dsimp [psi]
    rw [max_eq_left hmem.1]
    linarith
  have hgi : Integrable g teacher := sphere_integrable teacher g hg
  have hn := integral_weight_nonneg_of_slices teacher r g hr.measurable hg.measurable hgi
    (himb.all_slices_nonneg) psi hpsim hpsip
    (hgi.pos_part.mul_bdd (hpsim.comp hr.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall hpsib))
    (hgi.neg_part.mul_bdd (hpsim.comp hr.measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall hpsib))
  let V : Set (UnitSphere d) := r ⁻¹' Icc rvis 1
  have hV : MeasurableSet V := hr.measurable measurableSet_Icc
  have hpull : (fun w => psi (r w) * g w) =
      (fun w => k (r w) * g w - V.indicator (fun w => k rvis * g w) w) := by
    funext w
    have hm := twoSidedLatitude_mem pole w
    dsimp [psi, V]
    rw [max_eq_left hm.1]
    change (k (r w) - (Ici rvis).indicator (fun _ => k rvis) (r w)) * g w = _
    by_cases hw : rvis ≤ r w
    · rw [indicator_of_mem (s := Ici rvis) hw,
        indicator_of_mem (s := r ⁻¹' Icc rvis 1) (show w ∈ r ⁻¹' Icc rvis 1 from ⟨hw, hm.2⟩)]
      ring
    · have hw' : w ∉ r ⁻¹' Icc rvis 1 := fun h => hw h.1
      rw [indicator_of_notMem (s := Ici rvis) hw,
        indicator_of_notMem (s := r ⁻¹' Icc rvis 1) hw']
      ring
  have hkg : Integrable (fun w => k (r w) * g w) teacher :=
    sphere_integrable teacher _ ((hk.comp hr).mul hg)
  rw [hpull, integral_sub hkg ((hgi.const_mul (k rvis)).indicator hV),
    integral_indicator hV, integral_const_mul] at hn
  have hv := himb.visible_lower
  rw [slicedTransverseMoment_pairing] at hv
  have hmul := mul_le_mul_of_nonneg_left hv hki
  rw [activeLatitudeMinimum_eq O a himb.radius_pos.le himb.radius_lt_one.le,
    weightedTransverseMoment_pairing]
  dsimp [V, r, g, k] at hn hmul ⊢
  linarith

theorem weightedTransverseMoment_norm_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsFiniteMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    activeLatitudeMinimum O a rvis * gamma ≤ ‖weightedTransverseMoment O a pole teacher‖ := by
  apply (weightedTransverseMoment_lower O a pole teacher e rvis gamma himb).trans
  simpa [himb.unit] using real_inner_le_norm e (weightedTransverseMoment O a pole teacher)

theorem weightedTransverseMoment_ne_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (hactive : ∃ n ∈ O, a n ≠ 0)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    weightedTransverseMoment O a pole teacher ≠ 0 := by
  have hp := mul_pos (activeLatitudeMinimum_pos O a hO hactive
    himb.radius_pos himb.radius_lt_one.le) himb.margin_pos
  exact norm_pos_iff.mp (hp.trans_le (weightedTransverseMoment_norm_lower O a pole teacher
    e rvis gamma himb))

end PaperFormalization.MatrixFactorization
