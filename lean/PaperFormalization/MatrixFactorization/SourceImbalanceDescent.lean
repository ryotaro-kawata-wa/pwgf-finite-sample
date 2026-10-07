import PaperFormalization.MatrixFactorization.GaussianHermiteAssembly
import PaperFormalization.MatrixFactorization.GaussianVisibilitySpectrum
import PaperFormalization.MatrixFactorization.TransverseVisibility
import PaperFormalization.MatrixFactorization.TransverseRetractionObjective
import PaperFormalization.MatrixFactorization.TransverseSourcePath

/-! # Source two-sided imbalance gives genuine spherical transverse escape

The active block is any finite set of odd degrees. The original Borel-slice
imbalance and a nonzero active coefficient imply a positive actual Gaussian
signal. All Gaussian pairing and integrability premises have been discharged
before the full normalized objective is differentiated here.
-/

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The source Loewner inequality, represented by every ambient quadratic
form of the actual covariance matrix and the actual weighted teacher moment. -/
theorem source_visibility_matrix_ge_weightedMoment_outer {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] (s : Weight d) :
    0 ≤ inner Real (outer s s) (gaussianVisibilityMatrix O a pole teacher -
      outer (weightedTransverseMoment O a pole teacher) (weightedTransverseMoment O a pole teacher)) := by
  have hg := gaussianVisibilityMatrix_ge_mean_outer O a pole teacher s
  rwa [gaussianTransverseMean_eq_weightedMoment O a hO] at hg

theorem source_visibility_eigenvalue_ge_weightedMoment_sq {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher] :
    ‖weightedTransverseMoment O a pole teacher‖^2 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher := by
  have hg := gaussianVisibilityMaxEigenvalue_lower O a pole teacher
  rwa [gaussianTransverseMean_eq_weightedMoment O a hO] at hg

theorem source_imbalance_signal_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    (activeLatitudeMinimum O a rvis * gamma)^2 ≤
      transverseTeacherSignal O a pole e teacher := by
  have hb := weightedTransverseMoment_lower O a pole teacher e rvis gamma himb
  have hk : 0 ≤ activeLatitudeMinimum O a rvis := by
    rw [activeLatitudeMinimum_eq O a himb.radius_pos.le himb.radius_lt_one.le]
    exact activeLatitudeWeight_nonneg O a himb.radius_pos.le
  have hc : 0 ≤ activeLatitudeMinimum O a rvis * gamma := mul_nonneg hk himb.margin_pos.le
  have hj := transverseTeacherSignal_ge_mean_pairing_sq O a pole teacher e himb.tangent
  rw [gaussianTransverseMean_eq_weightedMoment O a hO] at hj
  exact (pow_le_pow_left₀ hc hb 2).trans hj

theorem source_imbalance_signal_pos {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0)
    (pole : UnitSphere d) (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    0 < transverseTeacherSignal O a pole e teacher := by
  have hk := activeLatitudeMinimum_pos O a hO
    hactive himb.radius_pos himb.radius_lt_one.le
  exact (sq_pos_of_pos (mul_pos hk himb.margin_pos)).trans_le
    (source_imbalance_signal_lower O a hO pole teacher e rvis gamma himb)

theorem source_imbalance_gaussian_mean_ne_zero {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    gaussianTransverseMean O a pole teacher ≠ 0 := by
  rw [gaussianTransverseMean_eq_weightedMoment O a hO]
  exact weightedTransverseMoment_ne_zero O a hO
    hactive pole teacher e rvis gamma himb

/-- The actual normalized objective has strictly negative second derivative
with the source's quantitative imbalance coefficient. -/
theorem source_imbalance_retracted_negative_curvature {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective O a P lambda p teacher teacher
    HasDerivAt F 0 0 ∧
      deriv (deriv F) 0 ≤ -2 * (activeLatitudeMinimum O a rvis * gamma)^2 ∧
      deriv (deriv F) 0 < 0 := by
  dsimp only
  have hd := transverse_retracted_objective_variations O a hO
    pole r hr hrpi e himb.tangent himb.unit lambda p hp teacher
  refine ⟨hd.1, ?_, ?_⟩
  · rw [hd.2.deriv]
    have hb := source_imbalance_signal_lower O a hO pole teacher e rvis gamma himb
    linarith
  · rw [hd.2.deriv]
    have hp := source_imbalance_signal_pos O a hO hactive pole teacher e rvis gamma himb
    linarith

/-- The coefficient in the full normalized objective's Peano expansion is
the actual positive Gaussian signal, now derived from source imbalance. -/
theorem source_imbalance_retracted_expansion {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective O a P lambda p teacher teacher
    0 < transverseTeacherSignal O a pole e teacher ∧
      (fun t => F t-F 0+transverseTeacherSignal O a pole e teacher*t^2)
        =o[𝓝 (0 : Real)] (fun t => t^2) := by
  exact ⟨source_imbalance_signal_pos O a hO hactive pole teacher e rvis gamma himb,
    transverse_retracted_objective_expansion O a hO pole r hr hrpi
      e himb.tangent himb.unit lambda p hp teacher⟩

/-- This is a theorem about the original normalized spherical pushforwards.
The positive-signal premise is discharged, not added to the manuscript. -/
theorem source_imbalance_retracted_strict_decrease {d h : Nat}
    (O : Finset Nat) (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let P := transverseCenterVariation pole r hr hrpi e
    let F := variationRetractedObjective O a P lambda p teacher teacher
    ∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 →
      F t ≤ F 0-((activeLatitudeMinimum O a rvis * gamma)^2/2)*t^2 ∧
      F t < F 0 := by
  have hd := transverse_retracted_strict_decrease O a hO
    pole r hr hrpi e himb.tangent himb.unit lambda p hp teacher
    (source_imbalance_signal_pos O a hO hactive pole teacher e rvis gamma himb)
  have hb := source_imbalance_signal_lower O a hO pole teacher e rvis gamma himb
  dsimp only at hd ⊢
  filter_upwards [hd] with t ht hne
  refine ⟨?_, (ht hne).2⟩
  exact (ht hne).1.trans (sub_le_sub_left
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hb (by norm_num))
      (sq_nonneg t)) _)

/-- The printed lower bound uses the largest eigenvalue of the actual
Gaussian visibility operator, not an assumed curvature parameter. -/
theorem source_imbalance_max_eigenvalue_lower {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    (activeLatitudeMinimum O a rvis * gamma)^2 ≤
      gaussianVisibilityMaxEigenvalue O a pole teacher := by
  have hb := weightedTransverseMoment_norm_lower O a pole teacher e rvis gamma himb
  have hk : 0 ≤ activeLatitudeMinimum O a rvis := by
    rw [activeLatitudeMinimum_eq O a himb.radius_pos.le himb.radius_lt_one.le]
    exact activeLatitudeWeight_nonneg O a himb.radius_pos.le
  have hl := gaussianVisibilityMaxEigenvalue_lower O a pole teacher
  rw [gaussianTransverseMean_eq_weightedMoment O a hO] at hl
  exact (pow_le_pow_left₀ (mul_nonneg hk himb.margin_pos.le) hb 2).trans hl

theorem source_imbalance_top_eigenvector {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d)
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma) :
    ∃ s : Weight d, ‖s‖ = 1 ∧ inner Real pole.val s = 0 ∧
      gaussianVisibilityOperator O a pole teacher s = gaussianVisibilityMaxEigenvalue O a pole teacher • s ∧
      transverseTeacherSignal O a pole s teacher = gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      (activeLatitudeMinimum O a rvis * gamma)^2 ≤ gaussianVisibilityMaxEigenvalue O a pole teacher ∧
      0 < gaussianVisibilityMaxEigenvalue O a pole teacher := by
  obtain ⟨s, hsn, hst, heig, hsig, _, hpos, _⟩ :=
    gaussianVisibility_exists_top_eigenvector O a pole teacher
      (source_imbalance_gaussian_mean_ne_zero O a hO hactive pole teacher e rvis gamma himb)
  exact ⟨s, hsn, hst, heig, hsig,
    source_imbalance_max_eigenvalue_lower O a hO pole teacher e rvis gamma himb, hpos⟩

/-- The source eigenvector produces the actual normalized path and the exact
escape coefficient in its full-objective expansion. -/
theorem source_imbalance_eigenvector_escape {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let escape := gaussianVisibilityMaxEigenvalue O a pole teacher
    ∃ s : Weight d, ‖s‖ = 1 ∧ inner Real pole.val s = 0 ∧
      gaussianVisibilityOperator O a pole teacher s = escape • s ∧
      (activeLatitudeMinimum O a rvis * gamma)^2 ≤ escape ∧ 0 < escape ∧
      let P := transverseCenterVariation pole r hr hrpi s
      let F := variationRetractedObjective O a P lambda p teacher teacher
      HasDerivAt F 0 0 ∧ HasDerivAt (deriv F) (-2*escape) 0 ∧
      (fun t => F t-F 0+escape*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      (∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 → F t ≤ F 0-(escape/2)*t^2 ∧ F t < F 0) := by
  dsimp only
  obtain ⟨s, hsn, hst, heig, hsig, hlo, hpos⟩ :=
    source_imbalance_top_eigenvector O a hO hactive pole teacher e rvis gamma himb
  refine ⟨s, hsn, hst, heig, hlo, hpos, ?_⟩
  have hd := transverse_retracted_objective_variations O a hO pole r hr hrpi s hst hsn
    lambda p hp teacher
  have hex := transverse_retracted_objective_expansion O a hO pole r hr hrpi s hst hsn
    lambda p hp teacher
  have hdec := transverse_retracted_strict_decrease O a hO pole r hr hrpi s hst hsn
    lambda p hp teacher (hsig ▸ hpos)
  rw [hsig] at hd hex hdec
  exact ⟨hd.1, hd.2, hex, hdec⟩

/-- The full source transverse escape construction: a smooth ambient field,
equal normalized marginals from the antipodal center, the original cap class,
the metric order `O(|t|^p)`, and the actual top-eigenvalue objective expansion.
Every property concerns the same original pushforward path. -/
theorem source_imbalance_transverse_escape {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (hO : ∀ n, n ∈ O → Odd n)
    (hactive : ∃ n ∈ O, a n ≠ 0) (pole : UnitSphere d) (r : Real)
    (hr : 0 < r) (hrpi : r < Real.pi/2) (teacher : Measure (UnitSphere d))
    [IsProbabilityMeasure teacher] (e : Weight d) (rvis gamma : Real)
    (himb : TwoSidedTeacherImbalance pole teacher e rvis gamma)
    (lambda p : Real) (hp : 2 < p) :
    let escape := gaussianVisibilityMaxEigenvalue O a pole teacher
    ∃ s : Weight d, ‖s‖ = 1 ∧ inner Real pole.val s = 0 ∧
      gaussianVisibilityOperator O a pole teacher s = escape • s ∧
      (activeLatitudeMinimum O a rvis * gamma)^2 ≤ escape ∧ 0 < escape ∧
      let P := transverseCenterVariation pole r hr hrpi s
      let F := variationRetractedObjective O a P lambda p teacher teacher
      ContDiff Real ⊤ (transverseHalfFieldAmbient s) ∧
      (∀ (i : Fin 2) (w : UnitSphere d), P.velocity i w = transverseHalfFieldAmbient s w.val) ∧
      (∀ i : Fin 2, (P.measure i).map
        (sphericalRetractFamily (P.velocity i) (P.tangent i) 0) = antipodalMeasure pole) ∧
      (∀ t : Real, (P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) t) =
        (P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) t)) ∧
      (∀ᶠ t in 𝓝 (0 : Real), ∀ i : Fin 2, TwoCapClass pole r
        ((P.measure i).map (sphericalRetractFamily (P.velocity i) (P.tangent i) t))) ∧
      variationRetractedRegularizer P lambda p =O[𝓝 (0 : Real)] (fun t => |t|^p) ∧
      variationRetractedRegularizer P lambda p =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      HasDerivAt F 0 0 ∧ HasDerivAt (deriv F) (-2*escape) 0 ∧
      (fun t => F t-F 0+escape*t^2) =o[𝓝 (0 : Real)] (fun t => t^2) ∧
      (∀ᶠ t in 𝓝 (0 : Real), t ≠ 0 → F t ≤ F 0-(escape/2)*t^2 ∧ F t < F 0) := by
  dsimp only
  obtain ⟨s, hsn, hst, heig, hlo, hpos, hjet⟩ :=
    source_imbalance_eigenvector_escape O a hO hactive pole r hr hrpi teacher e rvis gamma himb lambda p hp
  refine ⟨s, hsn, hst, heig, hlo, hpos, transverseHalfFieldAmbient_contDiff s, ?_, ?_, ?_, ?_, ?_, ?_, hjet⟩
  · intro i w
    rfl
  · exact transverseCenter_retract_initial pole r hr hrpi s
  · exact transverseCenter_retract_same_density pole r hr hrpi s
  · exact transverseCenter_retract_caps_near pole r hr hrpi s
  · exact transverse_retracted_regularizer_bigO pole r hr hrpi s hst hsn lambda p hp
  · exact transverse_retracted_regularizer_littleO pole r hr hrpi s hst hsn lambda p hp

end PaperFormalization.MatrixFactorization
