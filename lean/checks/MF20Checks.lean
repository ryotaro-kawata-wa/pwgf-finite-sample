import PaperFormalization.MatrixFactorization.SourceRadialCoercivity
import PaperFormalization.MatrixFactorization.AntisymmetricSourceFittingBound

/-! MF20 boundary diagnostics for actual weighted fourth norms and source
coefficients. Zero weights and zero transport are retained, and source
smallness is tested at equality rather than replaced by a strict margin. -/
open MeasureTheory ProbabilityTheory Set Filter Function
namespace PaperFormalization.MatrixFactorization.MF20BoundaryChecks
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- 1. The finite-measure fourth-moment theorem includes the zero original measure.
example {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] (F : A → E) :
    norm (∫ w, F w ∂(0 : Measure A))^4 ≤
      ((0 : Measure A).real univ)^3*(∫ w, norm (F w)^4 ∂(0 : Measure A)) :=
  finiteMeasure_norm_integral_fourth_le 0 F (by simp) (by simp)

-- 2. Zero density has zero mass without dividing by that mass.
example {A : Type*} [MeasurableSpace A] (mu : Measure A) :
    (mu.withDensity (fun _w => ENNReal.ofReal (0 : Real))).real univ = 0 := by
  simpa only [integral_zero] using withDensity_ofReal_mass mu (fun _w => (0 : Real)) (fun _w => le_rfl)
    measurable_const (integrable_zero _ _ _)

-- 3. A zero uniform L4 bound forces the actual finite average norm to vanish.
example {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) [IsFiniteMeasure mu] (gamma : Measure B) [SFinite gamma]
    (F : A → B → E) (hF : Integrable (uncurry F) (mu.prod gamma))
    (h4 : Integrable (fun wz : A × B => norm (F wz.1 wz.2)^4) (mu.prod gamma))
    (hb : ∀ᵐ w ∂mu, lpNorm (F w) 4 gamma ≤ 0) :
    lpNorm (fun z => ∫ w, F w z ∂mu) 4 gamma = 0 := by
  have hh := finiteMeasure_lpNorm_four_average_le mu gamma F 0 le_rfl hF h4 hb
  exact le_antisymm (by simpa using hh) lpNorm_nonneg

-- 4. A zero weighting density annihilates any vector integrand, with no integrability supplied.
example {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    (mu : Measure A) (gamma : Measure B) (G : A → B → E) :
    lpNorm (fun z => ∫ w, (0 : Real) • G w z ∂mu) 4 gamma = 0 := by simp

-- 5. The actual time-density measure retains exactly the mass one-half.
example : (∫ _s, (1 : Real)
    ∂(volume.restrict (Icc (0 : Real) 1)).withDensity (fun s => ENNReal.ofReal s)) = 1/2 := by
  rw [unitInterval_timeWeight_integral]
  simp only [smul_eq_mul, mul_one]
  rw [integral_id]
  norm_num

-- 6. The stationary contraction has zero difference and zero endpoint-remainder norms.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (y : UnitSphere d) :
    lpNorm (fun z : Weight d => finiteHermiteActivation O a (inner Real y.val z) -
      finiteHermiteActivation O a (inner Real y.val z)) 4 (stdGaussian (Weight d)) = 0 ∧
    lpNorm (poleContractionFeatureRemainder O a y y) 4 (stdGaussian (Weight d)) = 0 := by
  constructor
  · simp
  · have hb := poleContractionFeatureRemainder_lpNorm_four_le O a y y
      (by simpa using Real.pi_pos)
    exact le_antisymm (by simpa using hb) lpNorm_nonneg

-- 7. A vanishing source K2 yields zero contraction remainder norm at every shortest endpoint.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) (hK : gaussianSecondJetL4 O a = 0) :
    lpNorm (poleContractionFeatureRemainder O a y w) 4 (stdGaussian (Weight d)) = 0 := by
  have hb := poleContractionFeatureRemainder_lpNorm_four_le O a y w hs
  exact le_antisymm (by simpa only [hK, zero_mul, zero_div] using hb) lpNorm_nonneg

-- 8. The true difference estimate has no oddness or cap premise.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (y w : UnitSphere d)
    (hs : sphericalDistance y w < Real.pi) :
    lpNorm (fun z : Weight d => finiteHermiteActivation O a (inner Real w.val z) -
      finiteHermiteActivation O a (inner Real y.val z)) 4 (stdGaussian (Weight d)) ≤
      gaussianFirstJetL4 O a*sphericalDistance y w :=
  poleContractionFeatureDifference_lpNorm_four_le O a y w hs

-- 9. The actual directional first jet is in L4 also for the zero tangent.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (w : UnitSphere d) :
    MemLp (fun z => inner Real (0 : Weight d) z • finiteHermiteActivationJet 1 O a
      (inner Real w.val z)) 4 (stdGaussian (Weight d)) :=
  (finiteHermite_directional_first_L4 O a w 0 (by simp)).1

-- 10. Joint Gaussian integrability is valid for a time measure concentrated at a negative time.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (y : UnitSphere d)
    (v : Weight d) (hv : inner Real y.val v = 0) :
    Integrable (fun sz : Real × Weight d => norm (sphericalFeatureSecond 0 O a y v hv sz.2 sz.1)^4)
      ((Measure.dirac (-2 : Real)).prod (stdGaussian (Weight d))) :=
  (sphericalFeature_jets_time_gaussian_integrable O a y v hv (Measure.dirac (-2 : Real))).2.2.2

-- 11. Initial assigned-pole cancellation occurs after averaging the original probability.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hcap : TwoCapClass pole r mu) (z : Weight d) :
    meanFeature (finiteHermiteActivation O a) mu z = ∫ w,
      finiteHermiteActivation O a (inner Real w.val z) -
        finiteHermiteActivation O a (inner Real (assignedPole pole w).val z) ∂mu :=
  meanFeature_eq_integral_assigned_difference O a hO pole r mu hcap z

-- 12. The original radius second moment is half the true product transport cost.
example {d : Nat} (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d))
    (hcap : TwoCapClass pole r mu) :
    (∫ w, sphericalPoleRadius pole w^2 ∂mu) =
      productAntipodalTransportSq pole mu (reflectedMeasure mu)/2 :=
  sphericalPoleRadius_sq_integral pole r mu hcap

-- 13. Zero transport yields a zero mean-feature norm without an unsupported pointwise radius claim.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (hZ : productAntipodalTransportSq pole mu (reflectedMeasure mu) = 0) :
    lpNorm (meanFeature (finiteHermiteActivation O a) mu) 4 (stdGaussian (Weight d)) = 0 := by
  have hb := antisymmetric_mean_lpNorm_four_le O a hO pole r mu hcap
  exact le_antisymm (by simpa [hZ] using hb) lpNorm_nonneg

-- 14. Zero transport also yields a zero actual averaged remainder norm.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (hZ : productAntipodalTransportSq pole mu (reflectedMeasure mu) = 0) :
    lpNorm (contractionMeanRemainder O a pole mu) 4 (stdGaussian (Weight d)) = 0 := by
  have hb := contractionMeanRemainder_lpNorm_four_le O a hO pole r mu hcap
  exact le_antisymm (by simpa [hZ] using hb) lpNorm_nonneg

-- 15. At zero product distance both actual fitting fields vanish at every sphere evaluation point.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hZ : productAntipodalTransportSq pole mu (reflectedMeasure mu) = 0)
    (i : Fin 2) (w : UnitSphere d) :
    sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w = 0 := by
  apply norm_eq_zero.mp
  have hb := antisymmetric_sphericalFittingGradient_norm_source O a hO pole r mu hcap teacher i w
  exact le_antisymm (by simpa [hZ] using hb) (norm_nonneg _)

-- 16. The actual fitting bound contains the literal source denominator sqrt(2).
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a mu (reflectedMeasure mu) teacher teacher i w) ≤
      ((gaussianFirstJetL4 O a)^2*((gaussianActivationL4 O a)^2+
        (teacherFeatureL4 d O a teacher)^2)/Real.sqrt 2)*
          Real.sqrt (productAntipodalTransportSq pole mu (reflectedMeasure mu)) :=
  antisymmetric_sphericalFittingGradient_norm_source O a hO pole r mu hcap teacher i w

-- 17. The actual radial fitting lower bound contains the literal source denominator 32.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r : Real) (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    -((gaussianSecondJetL4 O a)^2*((gaussianActivationL4 O a)^2+
      (teacherFeatureL4 d O a teacher)^2)/32)*
        (productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialFittingPairing O a pole mu teacher :=
  antisymmetricRadialFittingPairing_lower_source O a hO pole r mu hcap teacher

-- 18. Cubic regularization gives the real exponent 3/2 in the actual full radial bound.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r lambda : Real) (mu : Measure (UnitSphere d))
    (hcap : TwoCapClass pole r mu) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    lambda*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(3/2 : Real) -
      sourceRadialConstant d O a teacher*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricRadialObjectivePairing O a pole lambda 3 mu teacher :=
  antisymmetricRadialObjectivePairing_lower_source O a hO pole r lambda 3 (by norm_num) mu hcap teacher

-- 19. Equality at the printed source threshold is admitted; the margin is closed.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r lambda p : Real) (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (mu : Measure (UnitSphere d)) (hcap : TwoCapClass pole r mu)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (heq : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^((4-p)/2) = lambda/2) :
    (lambda/2)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p/2) ≤
      antisymmetricRadialObjectivePairing O a pole lambda p mu teacher ∧
    (lambda^2/4)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^(p-1) ≤
      antisymmetricGradientEnergy O a pole lambda p mu teacher :=
  ⟨antisymmetric_radial_pairing_source O a hO pole r lambda p hl hp hp4 mu hcap teacher heq.le,
    antisymmetricGradientEnergy_lower_source O a hO pole r lambda p hl hp hp4 mu hcap teacher heq.le⟩

-- 20. Zero distance is included in the cubic source energy bound; no energy cancellation is asserted.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n ∈ O, Odd n)
    (pole : UnitSphere d) (r lambda : Real) (hl : 0 < lambda) (mu : Measure (UnitSphere d))
    (hcap : TwoCapClass pole r mu) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (hZ : productAntipodalTransportSq pole mu (reflectedMeasure mu) = 0) :
    (lambda^2/4)*(productAntipodalTransportSq pole mu (reflectedMeasure mu))^2 ≤
      antisymmetricGradientEnergy O a pole lambda 3 mu teacher := by
  have hs : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole mu (reflectedMeasure mu))^((4-(3 : Real))/2) ≤ lambda/2 := by
    rw [hZ, Real.zero_rpow (by norm_num : (4-(3 : Real))/2 ≠ 0), mul_zero]
    positivity
  have hb := antisymmetricGradientEnergy_lower_source O a hO pole r lambda 3 hl
    (by norm_num) (by norm_num) mu hcap teacher hs
  norm_num only [show (3 : Real)-1 = 2 by norm_num, Real.rpow_two] at hb
  exact hb

end PaperFormalization.MatrixFactorization.MF20BoundaryChecks
