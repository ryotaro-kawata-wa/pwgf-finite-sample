import PaperFormalization.MatrixFactorization.GaussianVisibility
import PaperFormalization.MatrixFactorization.WeightedTransverseMoment
import PaperFormalization.MatrixFactorization.GaussianHermiteCrossCovariance

/-! # Gaussian and teacher integration for finite Hermite blocks

The finite activation is expanded with its original normalization. Explicit
polynomial envelopes justify exchanging the original sphere measure and the
Gaussian input before any covariance identity is applied.
-/

open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def pointTransversePairing {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (w : UnitSphere d) (z : Weight d) : Real :=
  inner Real (finiteHermiteActivation O a (inner Real w.val z))
    (transverseFeature O a pole s z)

theorem pointTransversePairing_continuous {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d) :
    Continuous (fun wz : UnitSphere d × Weight d => pointTransversePairing O a pole s wz.1 wz.2) := by
  unfold pointTransversePairing transverseFeature
  apply Continuous.inner
  · exact (finiteHermiteActivation_continuous O a).comp (by fun_prop)
  · exact (by fun_prop : Continuous (fun wz : UnitSphere d × Weight d =>
      (1/2 : Real) * inner Real s wz.2)).smul
      ((finiteHermiteActivationJet_continuous 1 O a).comp (by fun_prop))

theorem pointTransversePairing_bound {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (w : UnitSphere d) (z : Weight d) :
    ‖pointTransversePairing O a pole s w z‖ ≤
      (‖s‖ * activationJetMass 0 O a * activationJetMass 1 O a) *
        (1+‖z‖)^(hermiteJetOrder 0 O + hermiteJetOrder 1 O + 1) := by
  have h0 := finiteHermiteActivationJet_sphere_bound 0 O a w z
  rw [finiteHermiteActivationJet_zero] at h0
  have h1 := finiteHermiteActivationJet_sphere_bound 1 O a pole z
  have hs : |(1/2 : Real)*inner Real s z| ≤ ‖s‖ * (1+‖z‖) := by
    rw [abs_mul]
    norm_num
    have hi := abs_real_inner_le_norm s z
    have hn := norm_nonneg s
    have hnz := norm_nonneg z
    have ha := abs_nonneg (inner Real s z)
    nlinarith
  unfold pointTransversePairing
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ‖finiteHermiteActivation O a (inner Real w.val z)‖ *
        ‖transverseFeature O a pole s z‖ := abs_real_inner_le_norm _ _
    _ ≤ featureEnvelope 0 O a z *
        ((‖s‖*(1+‖z‖))*featureEnvelope 1 O a z) := by
      apply mul_le_mul h0 _ (norm_nonneg _) (featureEnvelope_nonneg 0 O a z)
      rw [transverseFeature, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hs h1 (norm_nonneg _) (by positivity)
    _ = _ := by unfold featureEnvelope; rw [pow_add, pow_add, pow_one]; ring

theorem pointTransversePairing_integrable_prod {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    Integrable (fun wz : UnitSphere d × Weight d => pointTransversePairing O a pole s wz.1 wz.2)
      (teacher.prod (stdGaussian (Weight d))) := by
  have hi := ((gaussian_one_add_norm_pow_integrable d
    (hermiteJetOrder 0 O + hermiteJetOrder 1 O + 1)).const_mul
    (‖s‖ * activationJetMass 0 O a * activationJetMass 1 O a)).comp_snd teacher
  apply hi.mono' (pointTransversePairing_continuous O a pole s).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun wz => pointTransversePairing_bound O a pole s wz.1 wz.2)

theorem gaussian_teacher_pairing_swap {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher] :
    (∫ z : Weight d, inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
      (transverseFeature O a pole s z) ∂stdGaussian (Weight d)) =
      ∫ w, ∫ z : Weight d, pointTransversePairing O a pole s w z
        ∂stdGaussian (Weight d) ∂teacher := by
  have he (z : Weight d) :
      inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (transverseFeature O a pole s z) = ∫ w, pointTransversePairing O a pole s w z ∂teacher := by
    have hi : Integrable (fun w : UnitSphere d => finiteHermiteActivation O a (inner Real w.val z)) teacher :=
      sphere_integrable teacher _ ((finiteHermiteActivation_continuous O a).comp
        (f := fun w : UnitSphere d => inner Real w.val z) (by fun_prop))
    rw [real_inner_comm, meanFeature, ← integral_inner hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => real_inner_comm _ _)
  simp_rw [he]
  exact integral_integral_swap (pointTransversePairing_integrable_prod O a pole s teacher).swap

theorem normalizedHermiteJet_sphere_growth {d : Nat} (k n : Nat)
    (w : UnitSphere d) (z : Weight d) :
    |normalizedHermiteJet k n (inner Real w.val z)| ≤
      hermiteJetMass k n * (1+‖z‖)^(((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).natDegree) := by
  have hi : |inner Real w.val z| ≤ ‖z‖ := by
    simpa only [unitSphere_norm, one_mul] using abs_real_inner_le_norm w.val z
  apply (normalizedHermiteJet_growth k n _ le_rfl _).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by linarith) _) (hermiteJetMass_nonneg k n)

theorem normalizedHermite_transverse_product_integrable {d : Nat}
    (n m : Nat) (w pole : UnitSphere d) (s : Weight d) :
    Integrable (fun z : Weight d => normalizedHermite n (inner Real w.val z) *
      inner Real s z * normalizedHermiteJet 1 m (inner Real pole.val z))
      (stdGaussian (Weight d)) := by
  let f := fun z : Weight d => normalizedHermite n (inner Real w.val z) *
    inner Real s z * normalizedHermiteJet 1 m (inner Real pole.val z)
  let N := (hermiteRealPolynomial n).natDegree +
    (Polynomial.derivative (hermiteRealPolynomial m)).natDegree + 1
  let C := hermiteJetMass 0 n * ‖s‖ * hermiteJetMass 1 m
  have hf : Continuous f := ((normalizedHermite_continuous n).comp
    (f := fun z : Weight d => inner Real w.val z) (by fun_prop)).mul
    (by fun_prop) |>.mul ((normalizedHermiteJet_continuous 1 m).comp
      (f := fun z : Weight d => inner Real pole.val z) (by fun_prop))
  have hb (z : Weight d) : ‖f z‖ ≤ C*(1+‖z‖)^N := by
    have h0 := normalizedHermiteJet_sphere_growth 0 n w z
    simp only [normalizedHermiteJet_zero, Function.iterate_zero, id_eq] at h0
    have h1 := normalizedHermiteJet_sphere_growth 1 m pole z
    simp only [Function.iterate_one] at h1
    have hs : |inner Real s z| ≤ ‖s‖*(1+‖z‖) :=
      (abs_real_inner_le_norm s z).trans (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg s))
    rw [Real.norm_eq_abs]
    dsimp [f]
    rw [abs_mul, abs_mul]
    have hm := mul_le_mul (mul_le_mul h0 hs (abs_nonneg _)
      (mul_nonneg (hermiteJetMass_nonneg 0 n) (by positivity))) h1
      (abs_nonneg _) (by positivity [hermiteJetMass_nonneg 0 n])
    apply hm.trans_eq
    dsimp [C, N]
    rw [pow_add, pow_add, pow_one]
    ring
  have hi := gaussian_of_polynomial_bound f hf.stronglyMeasurable C
    (by dsimp [C]; positivity [hermiteJetMass_nonneg 0 n, hermiteJetMass_nonneg 1 m]) N 1 hb
  simp only [pow_one] at hi
  exact (integrable_norm_iff hf.aestronglyMeasurable).mp hi

theorem pointTransversePairing_sum {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (s : Weight d)
    (w : UnitSphere d) (z : Weight d) :
    pointTransversePairing O a pole s w z =
      ∑ n ∈ O, ∑ m ∈ O, ((1/2 : Real)*inner Real (a n) (a m)) *
        (normalizedHermite n (inner Real w.val z) * inner Real s z *
          normalizedHermiteJet 1 m (inner Real pole.val z)) := by
  simp only [pointTransversePairing, transverseFeature, finiteHermiteActivation,
    finiteHermiteActivationJet, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Finite-sum assembly from scalar Hermite covariance. The analytic premise
is exposed here so that the source endpoint can discharge it with the separate
Gaussian cross-covariance theorem. -/
theorem pointTransversePairing_integral_of_scalar_pairing {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole w : UnitSphere d) (s : Weight d) (hs : inner Real pole.val s = 0)
    (hpair : ∀ n m : Nat,
      (∫ z : Weight d, normalizedHermite n (inner Real w.val z) * inner Real s z *
        normalizedHermiteJet 1 m (inner Real pole.val z) ∂stdGaussian (Weight d)) =
        if n = m then (n : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0) :
    (∫ z : Weight d, pointTransversePairing O a pole s w z ∂stdGaussian (Weight d)) =
      activeLatitudeWeight O a (twoSidedLatitude pole w) *
        inner Real s (teacherTransverseProjection pole w) := by
  classical
  let f := fun n m : Nat => fun z : Weight d =>
    ((1/2 : Real)*inner Real (a n) (a m)) *
      (normalizedHermite n (inner Real w.val z) * inner Real s z *
        normalizedHermiteJet 1 m (inner Real pole.val z))
  have hi (n m : Nat) : Integrable (f n m) (stdGaussian (Weight d)) :=
    (normalizedHermite_transverse_product_integrable n m w pole s).const_mul _
  have hsum : (∫ z : Weight d, pointTransversePairing O a pole s w z ∂stdGaussian (Weight d)) =
      ∑ n ∈ O, ∑ m ∈ O, ((1/2 : Real)*inner Real (a n) (a m)) *
        (if n = m then (n : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0) := by
    simp_rw [pointTransversePairing_sum]
    rw [integral_finsetSum O (fun n _ => integrable_finsetSum O (fun m _ => hi n m))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum O (fun m _ => hi n m)]
    apply Finset.sum_congr rfl
    intro m hm
    rw [integral_const_mul, hpair]
  rw [hsum]
  have hproj : inner Real s (teacherTransverseProjection pole w) = inner Real w.val s := by
    change inner Real s (transverseProjection pole w.val) = _
    rw [transverseProjection_pairing pole s w.val hs, real_inner_comm]
  rw [hproj, activeLatitudeWeight, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_eq_single n]
  · simp only [ite_true, real_inner_self_eq_norm_sq]
    have he : Even (n-1) := (hO n hn).tsub_odd (by decide : Odd (1 : Nat))
    rw [twoSidedLatitude, he.pow_abs, real_inner_comm pole.val w.val]
    ring
  · intro m hm hmn
    simp [Ne.symm hmn]
  · exact fun h => (h hn).elim

theorem gaussian_teacher_pairing_eq_weightedMoment_of_scalar_pairing {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (s : Weight d) (hs : inner Real pole.val s = 0)
    (hpair : ∀ (w : UnitSphere d) (n m : Nat),
      (∫ z : Weight d, normalizedHermite n (inner Real w.val z) * inner Real s z *
        normalizedHermiteJet 1 m (inner Real pole.val z) ∂stdGaussian (Weight d)) =
        if n = m then (n : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0) :
    (∫ z : Weight d, inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
      (transverseFeature O a pole s z) ∂stdGaussian (Weight d)) =
      inner Real s (weightedTransverseMoment O a pole teacher) := by
  rw [gaussian_teacher_pairing_swap, weightedTransverseMoment_pairing]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun w =>
    pointTransversePairing_integral_of_scalar_pairing O a hO pole w s hs (hpair w))

/-- Equality of the actual transverse vectors follows from tangent pairings.
Testing the difference against itself avoids adding a basis or dimension
assumption to the original sphere model. -/
theorem gaussianTransverseMean_eq_weightedMoment_of_scalar_pairing {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hpair : ∀ (w : UnitSphere d) (s : Weight d), inner Real pole.val s = 0 → ∀ n m : Nat,
      (∫ z : Weight d, normalizedHermite n (inner Real w.val z) * inner Real s z *
        normalizedHermiteJet 1 m (inner Real pole.val z) ∂stdGaussian (Weight d)) =
        if n = m then (n : Real)*(inner Real w.val pole.val)^(n-1)*inner Real w.val s else 0) :
    gaussianTransverseMean O a pole teacher = weightedTransverseMoment O a pole teacher := by
  let v := gaussianTransverseMean O a pole teacher - weightedTransverseMoment O a pole teacher
  have hv : inner Real pole.val v = 0 := by
    simp only [v, inner_sub_right, gaussianTransverseMean_tangent, weightedTransverseMoment_tangent, sub_zero]
  have hleft : inner Real v (gaussianTransverseMean O a pole teacher) =
      ∫ z : Weight d, inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
        (transverseFeature O a pole v z) ∂stdGaussian (Weight d) := by
    rw [gaussianTransverseMean, ← integral_inner (gaussianTransverseVector_integrable O a pole teacher)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => gaussianTransverseVector_pairing O a pole teacher v z hv)
  have hr := gaussian_teacher_pairing_eq_weightedMoment_of_scalar_pairing O a hO pole teacher v hv
    (fun w => hpair w v hv)
  have hself : inner Real v v = 0 := by
    rw [show v = gaussianTransverseMean O a pole teacher - weightedTransverseMoment O a pole teacher from rfl,
      inner_sub_right]
    change inner Real v (gaussianTransverseMean O a pole teacher) -
      inner Real v (weightedTransverseMoment O a pole teacher) = 0
    rw [hleft, hr, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hself)

/-- The source finite-block point pairing, with the scalar Gaussian identity
fully proved rather than retained as an assumption. -/
theorem pointTransversePairing_integral {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole w : UnitSphere d)
    (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, pointTransversePairing O a pole s w z ∂stdGaussian (Weight d)) =
      activeLatitudeWeight O a (twoSidedLatitude pole w) *
        inner Real s (teacherTransverseProjection pole w) :=
  pointTransversePairing_integral_of_scalar_pairing O a hO pole w s hs
    (fun n m => normalizedHermite_gaussian_transverse_pairing n m w pole s hs)

theorem gaussian_teacher_pairing_eq_weightedMoment {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsFiniteMeasure teacher]
    (s : Weight d) (hs : inner Real pole.val s = 0) :
    (∫ z : Weight d, inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
      (transverseFeature O a pole s z) ∂stdGaussian (Weight d)) =
      inner Real s (weightedTransverseMoment O a pole teacher) :=
  gaussian_teacher_pairing_eq_weightedMoment_of_scalar_pairing O a hO pole teacher s hs
    (fun w n m => normalizedHermite_gaussian_transverse_pairing n m w pole s hs)

/-- The actual Gaussian mean equals the source weighted transverse moment
for every finite odd block and original teacher probability measure. -/
theorem gaussianTransverseMean_eq_weightedMoment {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    gaussianTransverseMean O a pole teacher = weightedTransverseMoment O a pole teacher :=
  gaussianTransverseMean_eq_weightedMoment_of_scalar_pairing O a hO pole teacher
    (fun w s hs n m => normalizedHermite_gaussian_transverse_pairing n m w pole s hs)

end PaperFormalization.MatrixFactorization
