import Mathlib

/-! # MF01: actual sphere measures and raw tensor moments

Executed validation and its scope are recorded in MF01_VALIDATION.md.
Source: EMN_problem_settings_v4 and EMN_rewrite_active_ambient_reduction_v4.
The tensors use their full finite Euclidean coordinate representation. A
permutation-invariance lemma records symmetry; no finite-moment injectivity of
probability measures is asserted. The sphere below has its subspace topology;
its inherited chordal distance is NOT named the spherical transport distance.
-/

open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

abbrev Weight (d : Nat) := EuclideanSpace Real (Fin d)
abbrev UnitSphere (d : Nat) := Metric.sphere (0 : Weight d) 1
abbrev MomentTensor (d n : Nat) := EuclideanSpace Real (Fin n -> Fin d)

instance unitSphereCompact (d : Nat) : CompactSpace (UnitSphere d) := by
  rw [UnitSphere, <- isCompact_iff_compactSpace]
  exact isCompact_sphere (0 : Weight d) 1

def reflect {d : Nat} (w : UnitSphere d) : UnitSphere d :=
  .mk (-w.val) (by simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using w.property)

@[simp] theorem reflect_val {d : Nat} (w : UnitSphere d) :
    (reflect w).val = -w.val := rfl

@[simp] theorem reflect_reflect {d : Nat} (w : UnitSphere d) :
    reflect (reflect w) = w := by
  apply Subtype.ext
  simp [reflect]

theorem reflect_continuous (d : Nat) : Continuous (@reflect d) := by
  exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

theorem reflect_measurable (d : Nat) : Measurable (@reflect d) :=
  (reflect_continuous d).measurable

noncomputable def reflectedMeasure {d : Nat} (mu : Measure (UnitSphere d)) :
    Measure (UnitSphere d) := mu.map reflect

instance reflectedMeasure_probability {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] : IsProbabilityMeasure (reflectedMeasure mu) :=
  Measure.isProbabilityMeasure_map (reflect_measurable d).aemeasurable

theorem reflectedMeasure_involutive {d : Nat} (mu : Measure (UnitSphere d)) :
    reflectedMeasure (reflectedMeasure mu) = mu := by
  unfold reflectedMeasure
  rw [Measure.map_map (reflect_measurable d) (reflect_measurable d)]
  simp only [Function.comp_def, reflect_reflect, Measure.map_id']

/-- Compactness gives genuine Bochner integrability before any moment is used. -/
theorem sphere_integrable {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (f : UnitSphere d -> E) (hf : Continuous f) : Integrable f mu := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (UnitSphere d))).exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun w => hC w (Set.mem_univ w)))

theorem integral_reflectedMeasure {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure (UnitSphere d)) (f : UnitSphere d -> E) (hf : Continuous f) :
    integral (reflectedMeasure mu) f = integral mu (fun w => f (reflect w)) := by
  exact integral_map (reflect_measurable d).aemeasurable hf.aestronglyMeasurable

noncomputable def antipodalMeasure {d : Nat} (a : UnitSphere d) : Measure (UnitSphere d) :=
  ((1/2 : ENNReal) • Measure.dirac a) + ((1/2 : ENNReal) • Measure.dirac (reflect a))

instance antipodalMeasure_probability {d : Nat} (a : UnitSphere d) :
    IsProbabilityMeasure (antipodalMeasure a) where
  measure_univ := by
    norm_num [antipodalMeasure, Measure.add_apply, Measure.smul_apply,
      ENNReal.inv_two_add_inv_two]

theorem reflectedMeasure_antipodal {d : Nat} (a : UnitSphere d) :
    reflectedMeasure (antipodalMeasure a) = antipodalMeasure a := by
  simp [reflectedMeasure, antipodalMeasure, Measure.map_add, Measure.map_smul,
    reflect_measurable, add_comm]

noncomputable def tensorPower {d : Nat} (n : Nat) (w : Weight d) : MomentTensor d n :=
  WithLp.toLp 2 (fun I => Finset.univ.prod (fun j : Fin n => w (I j)))

@[simp] theorem tensorPower_apply {d n : Nat} (w : Weight d) (I : Fin n -> Fin d) :
    tensorPower n w I = Finset.univ.prod (fun j : Fin n => w (I j)) := rfl

theorem tensorPower_continuous (d n : Nat) : Continuous (@tensorPower d n) := by
  unfold tensorPower
  fun_prop

/-- All raw orders, including n=0. Oddness is not assumed in this identity. -/
theorem tensorPower_neg {d : Nat} (n : Nat) (w : Weight d) :
    tensorPower n (-w) = ((-1 : Real)^n) • tensorPower n w := by
  apply PiLp.ext
  intro I
  change Finset.univ.prod (fun j : Fin n => -(w (I j))) =
    (-1 : Real)^n * Finset.univ.prod (fun j : Fin n => w (I j))
  simp only [Finset.prod_neg, Finset.card_univ, Fintype.card_fin]

/-- The coordinate representative belongs to the symmetric tensor subspace. -/
theorem tensorPower_permutation {d n : Nat} (w : Weight d)
    (I : Fin n -> Fin d) (e : Equiv.Perm (Fin n)) :
    tensorPower n w (I.comp e) = tensorPower n w I := by
  unfold tensorPower
  change Finset.univ.prod (fun j : Fin n => w (I (e j))) =
    Finset.univ.prod (fun j : Fin n => w (I j))
  apply Finset.prod_bij (fun j _ => e j)
  . intro j hj
    exact Finset.mem_univ _
  . intro j hj k hk hjk
    exact e.injective hjk
  . intro k hk
    exact .intro (e.symm k) (.intro (Finset.mem_univ _) (e.apply_symm_apply k))
  . intro j hj
    rfl

noncomputable def rawMoment {d : Nat} (mu : Measure (UnitSphere d)) (n : Nat) :
    MomentTensor d n := integral mu (fun w => tensorPower n w.val)

theorem rawMoment_integrable {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (n : Nat) :
    Integrable (fun w : UnitSphere d => tensorPower n w.val) mu :=
  sphere_integrable mu _ ((tensorPower_continuous d n).comp continuous_subtype_val)

/-- The zeroth moment has the original probability normalization. -/
theorem rawMoment_zero_apply {d : Nat} (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (I : Fin 0 -> Fin d) : rawMoment mu 0 I = 1 := by
  change (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 0 -> Fin d => Real) I)
    (integral mu (fun w => tensorPower 0 w.val)) = 1
  rw [<- (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin 0 -> Fin d => Real) I).integral_comp_comm
    (rawMoment_integrable mu 0)]
  simp [tensorPower]

/-- Integration preserves permutation symmetry of the raw tensor coordinates. -/
theorem rawMoment_permutation {d n : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (I : Fin n -> Fin d) (e : Equiv.Perm (Fin n)) :
    rawMoment mu n (I.comp e) = rawMoment mu n I := by
  change (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n -> Fin d => Real) (I.comp e))
      (integral mu (fun w => tensorPower n w.val)) =
    (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n -> Fin d => Real) I)
      (integral mu (fun w => tensorPower n w.val))
  rw [<- (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n -> Fin d => Real) (I.comp e)).integral_comp_comm
      (rawMoment_integrable mu n),
    <- (PiLp.proj (𝕜 := Real) 2 (fun _ : Fin n -> Fin d => Real) I).integral_comp_comm
      (rawMoment_integrable mu n)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w => tensorPower_permutation w.val I e)

theorem rawMoment_reflected {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (n : Nat) :
    rawMoment (reflectedMeasure mu) n = ((-1 : Real)^n) • rawMoment mu n := by
  unfold rawMoment
  rw [integral_reflectedMeasure mu (fun w : UnitSphere d => tensorPower n w.val)
    ((tensorPower_continuous d n).comp continuous_subtype_val)]
  simp only [reflect_val, tensorPower_neg, integral_smul]

theorem rawMoment_reflected_odd {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (n : Nat) (hn : Odd n) :
    rawMoment (reflectedMeasure mu) n = -rawMoment mu n := by
  rw [rawMoment_reflected, hn.neg_one_pow]
  simp

theorem rawMoment_antipodal_odd {d : Nat} (a : UnitSphere d) (n : Nat) (hn : Odd n) :
    rawMoment (antipodalMeasure a) n = 0 := by
  have h := rawMoment_reflected_odd (antipodalMeasure a) n hn
  rw [reflectedMeasure_antipodal] at h
  apply PiLp.ext
  intro I
  have hc := congrArg (fun z : MomentTensor d n => z I) h
  simp only [PiLp.neg_apply] at hc
  change rawMoment (antipodalMeasure a) n I = 0
  linarith

noncomputable def symmetricMoment {d : Nat} (mu nu : Measure (UnitSphere d)) (n : Nat) :
    MomentTensor d n := (1/2 : Real) • (rawMoment mu n + rawMoment nu n)

noncomputable def antisymmetricMoment {d : Nat} (mu nu : Measure (UnitSphere d)) (n : Nat) :
    MomentTensor d n := (1/2 : Real) • (rawMoment mu n - rawMoment nu n)

theorem rawMoment_left_reconstruction {d : Nat} (mu nu : Measure (UnitSphere d)) (n : Nat) :
    symmetricMoment mu nu n + antisymmetricMoment mu nu n = rawMoment mu n := by
  ext I
  simp only [symmetricMoment, antisymmetricMoment, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

theorem rawMoment_right_reconstruction {d : Nat} (mu nu : Measure (UnitSphere d)) (n : Nat) :
    symmetricMoment mu nu n - antisymmetricMoment mu nu n = rawMoment nu n := by
  ext I
  simp only [symmetricMoment, antisymmetricMoment, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

/-- Forward implication only: finite active moments are not measure coordinates. -/
theorem reflected_branch_symmetric_zero {d : Nat} (mu : Measure (UnitSphere d))
    [IsFiniteMeasure mu] (n : Nat) (hn : Odd n) :
    symmetricMoment mu (reflectedMeasure mu) n = 0 := by
  simp [symmetricMoment, rawMoment_reflected_odd mu n hn]

theorem same_density_antisymmetric_zero {d : Nat} (mu : Measure (UnitSphere d)) (n : Nat) :
    antisymmetricMoment mu mu n = 0 := by simp [antisymmetricMoment]

theorem antipodal_active_origin {d : Nat} (a : UnitSphere d) (O : Finset Nat)
    (hO : forall n, n ∈ O -> Odd n) :
    forall n, n ∈ O ->
      symmetricMoment (antipodalMeasure a) (antipodalMeasure a) n = 0 ∧
      antisymmetricMoment (antipodalMeasure a) (antipodalMeasure a) n = 0 := by
  intro n hn
  constructor
  . simp [symmetricMoment, rawMoment_antipodal_odd a n (hO n hn)]
  . exact same_density_antisymmetric_zero _ _

end PaperFormalization.MatrixFactorization
