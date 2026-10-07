import PaperFormalization.MatrixFactorization.FittingRays

/-! # MF01: source-facing fitting identities on the product sphere model

The finite activation, Gaussian input and genuine sphere
marginals are supplied explicitly. No integrability, covariance or fitting
identity is assumed by the source-facing results. Cap conditions are unnecessary
for these fitting-only identities and may be imposed by downstream callers.

This checkpoint does NOT prove the metric regularizer equals a fixed assignment
cost, the complete spherical first/second variations, or the four local geometry
claims. In particular fitting stationarity is not advertised as full WGF
stationarity. See MF01_CLAIM_MAP.md and the next-chat handoff.
-/

open MeasureTheory ProbabilityTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The literal unregularized matrix-product objective under N(0,I_d). -/
noncomputable def modelFitting {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) : Real :=
  let sigma := finiteHermiteActivation O a
  fittingEnergy (stdGaussian (Weight d))
    (fun z => outer (meanFeature sigma teacher1 z) (meanFeature sigma teacher2 z))
    (meanFeature sigma mu1) (meanFeature sigma mu2)

/-- This is the actual integrand in modelFitting, not an abstract certificate. -/
theorem modelFitting_integrable {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    Integrable (fun z : Weight d =>
      norm (outer (meanFeature (finiteHermiteActivation O a) mu1 z)
                   (meanFeature (finiteHermiteActivation O a) mu2 z) -
            outer (meanFeature (finiteHermiteActivation O a) teacher1 z)
                   (meanFeature (finiteHermiteActivation O a) teacher2 z))^2)
      (stdGaussian (Weight d)) := by
  let sigma := finiteHermiteActivation O a
  have hm (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      StronglyMeasurable (meanFeature sigma mu) :=
    meanFeature_stronglyMeasurable sigma (finiteHermiteActivation_continuous O a) mu
  have hi (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      Integrable (fun z => norm (meanFeature sigma mu z)^4) (stdGaussian (Weight d)) :=
    finiteHermite_mean_fourth_integrable O a mu
  exact fittingEnergy_integrable _ _ _ _
    (outer_stronglyMeasurable _ _ (hm teacher1) (hm teacher2)) (hm mu1) (hm mu2)
    (outer_sq_integrable _ _ _ (hm teacher1) (hm teacher2) (hi teacher1) (hi teacher2))
    (hi mu1) (hi mu2)

theorem modelFitting_nonneg {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d)) :
    0<=modelFitting O a mu1 mu2 teacher1 teacher2 :=
  fittingEnergy_nonneg _ _ _ _

@[simp] theorem modelFitting_teacher {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (teacher1 teacher2 : Measure (UnitSphere d)) :
    modelFitting O a teacher1 teacher2 teacher1 teacher2=0 := by
  exact fittingEnergy_exact _ _ _

/-- Actual fitting minimum on probability marginals. This is not a claim that
the teacher minimizes or is stationary for the REGULARIZED objective. -/
theorem modelFitting_teacher_isLeast {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (teacher : ProbabilityMeasure (UnitSphere d)) :
    IsLeast (Set.range (fun p : ProbabilityMeasure (UnitSphere d) × ProbabilityMeasure (UnitSphere d) =>
      modelFitting (d := d) O a p.1 p.2 teacher teacher)) 0 := by
  constructor
  . exact .intro (teacher,teacher) (modelFitting_teacher (d := d) O a teacher teacher)
  . rintro y ⟨p, rfl⟩
    exact modelFitting_nonneg (d := d) O a p.1 p.2 teacher teacher

/-- The distinguished antipodal pair has zero output in both factors. -/
theorem modelFitting_antipodal_origin {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    modelFitting O a (antipodalMeasure pole) (antipodalMeasure pole) teacher teacher =
      (1/2 : Real)*integral (stdGaussian (Weight d))
        (fun z => norm (meanFeature (finiteHermiteActivation O a) teacher z)^4) := by
  have hzero : meanFeature (finiteHermiteActivation O a) (antipodalMeasure pole) =
      fun _ : Weight d => 0 := by
    funext z
    exact finiteHermite_mean_antipodal O a hO pole z
  simp only [modelFitting, hzero, fittingEnergy_origin]
  have heq (z : Weight d) :
      norm (outer (meanFeature (finiteHermiteActivation O a) teacher z)
                  (meanFeature (finiteHermiteActivation O a) teacher z))^2 =
      norm (meanFeature (finiteHermiteActivation O a) teacher z)^4 := by
    rw [outer_norm_sq]
    ring
  simp_rw [heq]

/-- Exact antisymmetric branch loss, with the original Gaussian integral. -/
theorem modelFitting_antibranch_decomposition {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure teacher] :
    modelFitting O a mu (reflectedMeasure mu) teacher teacher =
      (1/2 : Real)*integral (stdGaussian (Weight d))
        (fun z => norm (meanFeature (finiteHermiteActivation O a) teacher z)^4) +
      integral (stdGaussian (Weight d)) (fun z =>
        (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
                    (meanFeature (finiteHermiteActivation O a) mu z))^2) +
      (1/2 : Real)*integral (stdGaussian (Weight d))
        (fun z => norm (meanFeature (finiteHermiteActivation O a) mu z)^4) := by
  have hreflect : meanFeature (finiteHermiteActivation O a) (reflectedMeasure mu) =
      fun z => -meanFeature (finiteHermiteActivation O a) mu z := by
    funext z
    exact meanFeature_reflected _ (finiteHermiteActivation_continuous O a)
      (finiteHermiteActivation_odd O a hO) mu z
  simp only [modelFitting, hreflect]
  exact fittingEnergy_antisymmetric _ _ _
    (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) teacher)
    (meanFeature_stronglyMeasurable _ (finiteHermiteActivation_continuous O a) mu)
    (finiteHermite_mean_fourth_integrable O a teacher)
    (finiteHermite_mean_fourth_integrable O a mu)

/-- Fitting loss alone has its antisymmetric-branch minimum at the zero feature.
This does not replace the cap invariance and dissipation proof of local attraction. -/
theorem modelFitting_antibranch_lower_at_center {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n) (pole : UnitSphere d)
    (mu teacher : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure teacher] :
    modelFitting O a (antipodalMeasure pole) (antipodalMeasure pole) teacher teacher <=
      modelFitting O a mu (reflectedMeasure mu) teacher teacher := by
  rw [modelFitting_antipodal_origin O a hO pole teacher,
    modelFitting_antibranch_decomposition O a hO mu teacher]
  have hcross : 0 <= integral (stdGaussian (Weight d)) (fun z =>
      (inner Real (meanFeature (finiteHermiteActivation O a) teacher z)
                  (meanFeature (finiteHermiteActivation O a) mu z))^2) :=
    integral_nonneg (fun z => sq_nonneg _)
  have hquartic : 0 <= integral (stdGaussian (Weight d))
      (fun z => norm (meanFeature (finiteHermiteActivation O a) mu z)^4) :=
    integral_nonneg (fun z => pow_nonneg (norm_nonneg _) _)
  linarith

/-- No model-level moment or differentiability premise is needed for this
output-ray fitting derivative: both directions are actual finite-Hermite features. -/
theorem modelFitting_output_origin_first {d h : Nat}
    (O : Finset Nat) (a : Nat -> Weight h)
    (mu1 mu2 teacher1 teacher2 : Measure (UnitSphere d))
    [IsProbabilityMeasure mu1] [IsProbabilityMeasure mu2]
    [IsProbabilityMeasure teacher1] [IsProbabilityMeasure teacher2] :
    HasDerivAt (fun s : Real => fittingEnergy (stdGaussian (Weight d))
      (fun z => outer (meanFeature (finiteHermiteActivation O a) teacher1 z)
                       (meanFeature (finiteHermiteActivation O a) teacher2 z))
      (fun z => s • meanFeature (finiteHermiteActivation O a) mu1 z)
      (fun z => s • meanFeature (finiteHermiteActivation O a) mu2 z)) 0 0 := by
  let sigma := finiteHermiteActivation O a
  have hm (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      StronglyMeasurable (meanFeature sigma mu) :=
    meanFeature_stronglyMeasurable sigma (finiteHermiteActivation_continuous O a) mu
  have hi (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
      Integrable (fun z => norm (meanFeature sigma mu z)^4) (stdGaussian (Weight d)) :=
    finiteHermite_mean_fourth_integrable O a mu
  exact fittingEnergy_origin_first _ _ _ _
    (outer_stronglyMeasurable _ _ (hm teacher1) (hm teacher2)) (hm mu1) (hm mu2)
    (outer_sq_integrable _ _ _ (hm teacher1) (hm teacher2) (hi teacher1) (hi teacher2))
    (hi mu1) (hi mu2)

end PaperFormalization.MatrixFactorization
