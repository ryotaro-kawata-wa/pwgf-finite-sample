import PaperFormalization.MatrixFactorization.TeacherNeighborhoodGeometry
import PaperFormalization.MatrixFactorization.TransverseVisibility

/-! # Expectation continuity from the actual spherical transport infimum

Every estimate is first proved for arbitrary marginal-constrained couplings.
Taking the established real infimum then gives the Wasserstein bound without
postulating existence of an optimal plan or a coupling gluing theorem.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

theorem sphericalCoupling_integral_first {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {mu nu : Measure (UnitSphere d)} (gamma : SphericalCoupling mu nu)
    (f : UnitSphere d → E) (hf : Continuous f) :
    (∫ z, f z.1 ∂gamma.measure) = ∫ w, f w ∂mu := by
  calc
    _ = ∫ w, f w ∂gamma.measure.map Prod.fst :=
      (integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := congrArg (fun m => ∫ w, f w ∂m) gamma.first_marginal

theorem sphericalCoupling_integral_second {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {mu nu : Measure (UnitSphere d)} (gamma : SphericalCoupling mu nu)
    (f : UnitSphere d → E) (hf : Continuous f) :
    (∫ z, f z.2 ∂gamma.measure) = ∫ w, f w ∂nu := by
  calc
    _ = ∫ w, f w ∂gamma.measure.map Prod.snd :=
      (integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := congrArg (fun m => ∫ w, f w ∂m) gamma.second_marginal

/-- The first angular transport moment is bounded by its second moment. -/
theorem sphericalCoupling_distance_integral_sq_le {d : Nat}
    {mu nu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    (gamma : SphericalCoupling mu nu) :
    (∫ z, sphericalDistance z.1 z.2 ∂gamma.measure)^2 ≤ sphericalTransportCost gamma :=
  probability_integral_sq_ge_sq_integral gamma.measure
    (fun z => sphericalDistance z.1 z.2)
    (spherePair_integrable gamma.measure _ (sphericalDistance_continuous d))
    (sphericalTransportCost_integrable gamma)

/-- An arbitrary coupling bounds the difference of original expectations. -/
theorem sphericalCoupling_expectation_sub_norm_le {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {mu nu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    (gamma : SphericalCoupling mu nu) (f : UnitSphere d → E) (hf : Continuous f)
    (L : Real) (hL : 0 ≤ L)
    (hlip : ∀ w y, norm (f w-f y) ≤ L*sphericalDistance w y) :
    norm ((∫ w, f w ∂mu)-(∫ w, f w ∂nu)) ≤
      L*(∫ z, sphericalDistance z.1 z.2 ∂gamma.measure) := by
  have hi1 : Integrable (fun z : UnitSphere d × UnitSphere d => f z.1) gamma.measure :=
    spherePair_integrable gamma.measure _ (hf.comp continuous_fst)
  have hi2 : Integrable (fun z : UnitSphere d × UnitSphere d => f z.2) gamma.measure :=
    spherePair_integrable gamma.measure _ (hf.comp continuous_snd)
  rw [← sphericalCoupling_integral_first gamma f hf, ← sphericalCoupling_integral_second gamma f hf,
    ← integral_sub hi1 hi2]
  calc
    _ ≤ ∫ z, norm (f z.1-f z.2) ∂gamma.measure := norm_integral_le_integral_norm _
    _ ≤ ∫ z, L*sphericalDistance z.1 z.2 ∂gamma.measure := by
      exact integral_mono (hi1.sub hi2).norm
        ((spherePair_integrable gamma.measure _ (sphericalDistance_continuous d)).const_mul L)
        (fun z => hlip z.1 z.2)
    _ = _ := integral_const_mul _ _

theorem sphericalCoupling_expectation_sub_sq_le {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {mu nu : Measure (UnitSphere d)} [IsProbabilityMeasure mu]
    (gamma : SphericalCoupling mu nu) (f : UnitSphere d → E) (hf : Continuous f)
    (L : Real) (hL : 0 ≤ L)
    (hlip : ∀ w y, norm (f w-f y) ≤ L*sphericalDistance w y) :
    norm ((∫ w, f w ∂mu)-(∫ w, f w ∂nu))^2 ≤ L^2*sphericalTransportCost gamma := by
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (sphericalCoupling_expectation_sub_norm_le gamma f hf L hL hlip) 2
  rw [mul_pow] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (sphericalCoupling_distance_integral_sq_le gamma)
    (sq_nonneg L))

/-- This bound uses the actual infimum over all couplings, rather than a
chosen transport map or an optimal-plan existence assumption. -/
theorem sphericalWasserstein_expectation_sub_sq_le {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : UnitSphere d → E) (hf : Continuous f) (L : Real) (hL : 0 ≤ L)
    (hlip : ∀ w y, norm (f w-f y) ≤ L*sphericalDistance w y) :
    norm ((∫ w, f w ∂mu)-(∫ w, f w ∂nu))^2 ≤ L^2*sphericalWassersteinSq mu nu := by
  by_cases hL0 : L = 0
  · have hb := sphericalCoupling_expectation_sub_sq_le (productSphericalCoupling mu nu) f hf L hL hlip
    simpa only [hL0, zero_pow (by decide : 2 ≠ 0), zero_mul] using hb
  · have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hL0)
    have hLsq : 0 < L^2 := sq_pos_of_pos hLpos
    have hinf : norm ((∫ w, f w ∂mu)-(∫ w, f w ∂nu))^2/L^2 ≤ sphericalWassersteinSq mu nu := by
      apply le_csInf (sphericalTransportValues_nonempty mu nu)
      rintro c ⟨gamma, rfl⟩
      apply (div_le_iff₀ hLsq).mpr
      simpa only [mul_comm] using sphericalCoupling_expectation_sub_sq_le gamma f hf L hL hlip
    have hh := (div_le_iff₀ hLsq).mp hinf
    simpa only [mul_comm] using hh

/-- A usable Lipschitz estimate in the square root of the certified transport
cost. Probability and all needed integrability are derived at their source. -/
theorem sphericalWasserstein_expectation_sub_norm_le {d : Nat} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : UnitSphere d → E) (hf : Continuous f) (L : Real) (hL : 0 ≤ L)
    (hlip : ∀ w y, norm (f w-f y) ≤ L*sphericalDistance w y) :
    norm ((∫ w, f w ∂mu)-(∫ w, f w ∂nu)) ≤ L*Real.sqrt (sphericalWassersteinSq mu nu) := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (sphericalWassersteinSq_nonneg mu nu)]
  exact sphericalWasserstein_expectation_sub_sq_le mu nu f hf L hL hlip

/-- Continuity of the assigned-pole transport cost follows without a triangle
inequality for the Wasserstein infimum or any matching of cap labels. -/
theorem assignedCost_integral_sub_abs_le {d : Nat} (a : UnitSphere d)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    abs ((∫ w, assignedCost a w ∂mu)-(∫ w, assignedCost a w ∂nu)) ≤
      Real.pi*Real.sqrt (sphericalWassersteinSq mu nu) := by
  simpa only [Real.norm_eq_abs] using sphericalWasserstein_expectation_sub_norm_le mu nu
    (assignedCost a) (assignedCost_continuous a) Real.pi Real.pi_pos.le
    (fun w y => by simpa only [Real.norm_eq_abs] using assignedCost_sub_abs_le a w y)

/-- In the original cap class the actual optimal antipodal cost varies
continuously with the actual transport distance to another cap measure. -/
theorem sphericalWassersteinSq_antipodal_sub_abs_le {d : Nat} (a : UnitSphere d) (r : Real)
    (mu nu : Measure (UnitSphere d)) (hmu : TwoCapClass a r mu) (hnu : TwoCapClass a r nu) :
    abs (sphericalWassersteinSq mu (antipodalMeasure a)-sphericalWassersteinSq nu (antipodalMeasure a)) ≤
      2*Real.pi*Real.sqrt (sphericalWassersteinSq mu nu) := by
  letI : IsProbabilityMeasure mu := hmu.probability
  letI : IsProbabilityMeasure nu := hnu.probability
  rw [sphericalWassersteinSq_antipodal a r mu hmu, sphericalWassersteinSq_antipodal a r nu hnu,
    ← mul_sub, abs_mul]
  norm_num
  have hh := assignedCost_integral_sub_abs_le a mu nu
  linarith

/-- Product transport continuity at the same-density teacher, using a finite
proof-local constant and no Wasserstein triangle or optimal-plan hypothesis. -/
theorem productAntipodalTransportSq_teacher_sub_abs_le {d : Nat} (a : UnitSphere d) (r : Real)
    (mu1 mu2 teacher : Measure (UnitSphere d)) (hmu1 : TwoCapClass a r mu1)
    (hmu2 : TwoCapClass a r mu2) (hteacher : TwoCapClass a r teacher) :
    abs (productAntipodalTransportSq a mu1 mu2-productAntipodalTransportSq a teacher teacher) ≤
      4*Real.pi*Real.sqrt (sphericalWassersteinSq mu1 teacher+sphericalWassersteinSq mu2 teacher) := by
  letI : IsProbabilityMeasure mu1 := hmu1.probability
  letI : IsProbabilityMeasure mu2 := hmu2.probability
  letI : IsProbabilityMeasure teacher := hteacher.probability
  have h1 := sphericalWassersteinSq_antipodal_sub_abs_le a r mu1 teacher hmu1 hteacher
  have h2 := sphericalWassersteinSq_antipodal_sub_abs_le a r mu2 teacher hmu2 hteacher
  have hn1 := sphericalWassersteinSq_nonneg mu1 teacher
  have hn2 := sphericalWassersteinSq_nonneg mu2 teacher
  have hs1 : Real.sqrt (sphericalWassersteinSq mu1 teacher) ≤
      Real.sqrt (sphericalWassersteinSq mu1 teacher+sphericalWassersteinSq mu2 teacher) :=
    Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt (sphericalWassersteinSq mu2 teacher) ≤
      Real.sqrt (sphericalWassersteinSq mu1 teacher+sphericalWassersteinSq mu2 teacher) :=
    Real.sqrt_le_sqrt (by linarith)
  calc
    _ = abs ((sphericalWassersteinSq mu1 (antipodalMeasure a)-sphericalWassersteinSq teacher (antipodalMeasure a)) +
        (sphericalWassersteinSq mu2 (antipodalMeasure a)-sphericalWassersteinSq teacher (antipodalMeasure a))) := by
      congr 1
      unfold productAntipodalTransportSq
      ring
    _ ≤ abs (sphericalWassersteinSq mu1 (antipodalMeasure a)-sphericalWassersteinSq teacher (antipodalMeasure a)) +
        abs (sphericalWassersteinSq mu2 (antipodalMeasure a)-sphericalWassersteinSq teacher (antipodalMeasure a)) := abs_add_le _ _
    _ ≤ 2*Real.pi*Real.sqrt (sphericalWassersteinSq mu1 teacher) +
        2*Real.pi*Real.sqrt (sphericalWassersteinSq mu2 teacher) := add_le_add h1 h2
    _ ≤ _ := by
      have hp : 0 ≤ 2*Real.pi := by positivity
      have hb1 := mul_le_mul_of_nonneg_left hs1 hp
      have hb2 := mul_le_mul_of_nonneg_left hs2 hp
      nlinarith

end PaperFormalization.MatrixFactorization
