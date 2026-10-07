import PaperFormalization.MatrixFactorization.TeacherNeighborhoodCurvature
import PaperFormalization.MatrixFactorization.GaussianFeatureWasserstein

/-! Angular-transport and actual Gaussian feature boundary diagnostics. -/
open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped Topology
open PaperFormalization.MatrixFactorization
set_option autoImplicit false

-- Antipodes have angular distance pi; no step substitutes the chord length.
example {d : Nat} (w : UnitSphere d) : norm (w.val-(reflect w).val) ≤ Real.pi := by
  simpa only [sphericalDistance_antipode] using unitSphere_chord_le_sphericalDistance w (reflect w)
example {d : Nat} (w y : UnitSphere d) :
    Real.pi ≤ sphericalDistance w y+sphericalDistance y (reflect w) := by
  simpa only [sphericalDistance_antipode] using sphericalDistance_triangle w y (reflect w)
example {d : Nat} (pole w y : UnitSphere d) :
    abs (assignedCost pole w-assignedCost pole y) ≤ Real.pi*sphericalDistance w y :=
  assignedCost_sub_abs_le pole w y

-- The zero Lipschitz-constant branch does not divide by that constant.
example {d h : Nat} (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (f : UnitSphere d → Weight h) (hf : Continuous f)
    (hzero : ∀ w y, norm (f w-f y) ≤ 0) :
    (∫ w, f w ∂mu) = ∫ w, f w ∂nu := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hb := sphericalWasserstein_expectation_sub_norm_le mu nu f hf 0 le_rfl
    (fun w y => by simpa using hzero w y)
  exact le_antisymm (by simpa using hb) (norm_nonneg _)

-- A zero transport infimum identifies the actual finite-Hermite means without
-- requiring a separate theorem that zero transport identifies the measures.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hzero : sphericalWassersteinSq mu nu = 0) (z : Weight d) :
    meanFeature (finiteHermiteActivation O a) mu z = meanFeature (finiteHermiteActivation O a) nu z := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hb := finiteHermite_mean_wasserstein_norm_le O a mu nu z
  exact le_antisymm (by simpa only [hzero, Real.sqrt_zero, mul_zero] using hb) (norm_nonneg _)
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    meanFeature (finiteHermiteActivation O a) mu 0 = meanFeature (finiteHermiteActivation O a) nu 0 := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hb := finiteHermite_mean_wasserstein_norm_le O a mu nu 0
  exact le_antisymm (by simpa [featureFirstEnvelope] using hb) (norm_nonneg _)
example {d h : Nat} (a : Nat → Weight h) : gaussianFeatureLipschitzSq d 0 ∅ a = 0 := by
  simp [gaussianFeatureLipschitzSq, featureFirstEnvelope, featureEnvelope, activationJetMass]

-- Original odd activations have zero antipodal mean, including mixed degrees.
example {d h : Nat} (a : Nat → Weight h) (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivation {1,3} a) mu z) ≤
      featureFirstEnvelope 0 {1,3} a z*Real.sqrt (sphericalWassersteinSq mu (antipodalMeasure pole)) := by
  have hodd : ∀ n ∈ ({1,3} : Finset Nat), Odd n := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl <;> decide
  simpa only [finiteHermite_mean_antipodal {1,3} a hodd pole z, sub_zero] using
    finiteHermite_mean_wasserstein_norm_le {1,3} a mu (antipodalMeasure pole) z

-- The continuity foundation itself also covers even and constant degrees.
example {d h : Nat} (a : Nat → Weight h) (mu nu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation {0,2} a) mu z-
      meanFeature (finiteHermiteActivation {0,2} a) nu z)^2 ∂stdGaussian (Weight d)) ≤
      gaussianFeatureLipschitzSq d 0 {0,2} a*sphericalWassersteinSq mu nu :=
  finiteHermite_mean_gaussian_wasserstein_sq_le {0,2} a mu nu
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (mu nu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hzero : sphericalWassersteinSq mu nu = 0) :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) mu z-
      meanFeature (finiteHermiteActivation O a) nu z)^2 ∂stdGaussian (Weight d)) = 0 := by
  apply le_antisymm
  · simpa only [hzero, mul_zero] using finiteHermite_mean_gaussian_wasserstein_sq_le O a mu nu
  · exact integral_nonneg (fun z => sq_nonneg _)
example {d h : Nat} (a : Nat → Weight h) (mu nu : Measure (UnitSphere d)) (z : Weight d) :
    meanFeature (finiteHermiteActivation ∅ a) mu z-meanFeature (finiteHermiteActivation ∅ a) nu z = 0 := by
  simp [meanFeature, finiteHermiteActivation]
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
    (hodd : ∀ n ∈ O, Odd n) (pole : UnitSphere d)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] :
    (∫ z : Weight d, norm (meanFeature (finiteHermiteActivation O a) mu z)^2 ∂stdGaussian (Weight d)) ≤
      gaussianFeatureLipschitzSq d 0 O a*sphericalWassersteinSq mu (antipodalMeasure pole) := by
  simpa only [finiteHermite_mean_antipodal O a hodd pole, sub_zero] using
    finiteHermite_mean_gaussian_wasserstein_sq_le O a mu (antipodalMeasure pole)

-- Vanishing fitting constants do not cause a division-by-zero radius.
example (lambda kappa Zo : Real) (hl : 0 < lambda) (hk : 0 < kappa) (hz : 0 < Zo) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧ ∀ Z D : Real, 0 ≤ D → D < rho →
      |Z-Zo| ≤ 4*Real.pi*D → 0 < Z ∧ c ≤ lambda*kappa*Z^(1/4 : Real)-0*D :=
  teacher_curvature_margin_exists lambda kappa (1/4) Zo 0 hl hk (by norm_num) hz (by norm_num)

-- The same radius and margin work for all original cap states and fields.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (r : Real) (teacher : Measure (UnitSphere d)) (ht : TwoCapClass pole r teacher)
    (lambda : Real) (hl : 0 < lambda)
    (hZ : 0 < productAntipodalTransportSq pole teacher teacher) :
    ∃ rho c : Real, 0 < rho ∧ 0 < c ∧ ∀ P : SphericalVariation d,
      P.pole = pole → P.radius = r →
      sphericalWassersteinSq (P.measure 0) teacher+sphericalWassersteinSq (P.measure 1) teacher < rho^2 →
      c*variationEnergy P ≤
        deriv (deriv (variationRetractedObjective O a P lambda (5/2) teacher teacher)) 0 :=
  normalized_teacher_neighborhood_curvature O a pole r teacher ht lambda (5/2) hl (by norm_num) hZ

-- Original slice imbalance itself separates the teacher from the antipodal law.
example {d : Nat} (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    (e : Weight d) (rv gamma r : Real) (hi : TwoSidedTeacherImbalance pole teacher e rv gamma)
    (hc : TwoCapClass pole r teacher) : 0 < productAntipodalTransportSq pole teacher teacher :=
  hi.product_transport_pos r hc

-- Strictness requires positive L2 energy, while the uniform margin allows zero fields.
example {d h : Nat} (O : Finset Nat) (a : Nat → Weight h) (pole : UnitSphere d)
    (r : Real) (teacher : Measure (UnitSphere d)) (ht : TwoCapClass pole r teacher)
    (lambda p : Real) (hl : 0 < lambda) (hp : 2 < p)
    (hZ : 0 < productAntipodalTransportSq pole teacher teacher) :
    ∃ rho : Real, 0 < rho ∧ ∀ P : SphericalVariation d,
      P.pole = pole → P.radius = r →
      sphericalWassersteinSq (P.measure 0) teacher+sphericalWassersteinSq (P.measure 1) teacher < rho^2 →
      0 < variationEnergy P →
      0 < deriv (deriv (variationRetractedObjective O a P lambda p teacher teacher)) 0 :=
  normalized_teacher_neighborhood_positive O a pole r teacher ht lambda p hl hp hZ
