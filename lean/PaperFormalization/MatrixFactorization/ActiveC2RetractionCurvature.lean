import PaperFormalization.MatrixFactorization.ActiveC2Suprema
import PaperFormalization.MatrixFactorization.ActiveRetractionJetEquality

/-! # MF36: source-shaped curvature bound for a C2 active functional

The path is the actual source normalized retraction and the constant is the
compact-ball gradient/Hessian supremum expression in its Hilbert norm. The
remaining fitting-polynomial identity is not assumed to have been proved.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

/-- The retraction's initial active coordinates are the original raw moments. -/
theorem activeMomentMapAlongRetract_zero {d : Nat} (O : Finset Nat)
    (P : SphericalVariation d) :
    activeMomentMapAlongRetract O P.measure P.velocity P.tangent 0 =
      activeMomentMap O (P.measure 0) (P.measure 1) := by
  have hp (i : Fin 2) : sphericalRetractFamily (P.velocity i) (P.tangent i) 0 = id := by
    funext w
    exact sphericalRetract_zero w (P.velocity i w) (P.tangent i w)
  rw [activeMomentMapAlongRetract_eq]
  apply PiLp.ext
  intro i
  fin_cases i
  · apply Subtype.ext
    apply PiLp.ext
    intro n
    change symmetricMoment ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) 0))
      ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) 0)) n.val =
        symmetricMoment (P.measure 0) (P.measure 1) n.val
    rw [hp 0, hp 1, Measure.map_id, Measure.map_id]
  · apply Subtype.ext
    apply PiLp.ext
    intro n
    change antisymmetricMoment ((P.measure 0).map (sphericalRetractFamily (P.velocity 0) (P.tangent 0) 0))
      ((P.measure 1).map (sphericalRetractFamily (P.velocity 1) (P.tangent 1) 0)) n.val =
        antisymmetricMoment (P.measure 0) (P.measure 1) n.val
    rw [hp 0, hp 1, Measure.map_id, Measure.map_id]

/-- Exact second derivative and the printed degree-weighted supremum lower bound.
This theorem is for the supplied C2 functional J; it is not yet its fit instantiation. -/
theorem spherical_retraction_c2_active_curvature {d : Nat} (O : Finset Nat)
    (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J)
    (P : SphericalVariation d) (R : Real) (A : ActiveMomentSpace d O)
    (hbase : activeMomentMap O (P.measure 0) (P.measure 1) = activeAntisymmetricPoint A)
    (hA : ‖A‖ ≤ R) :
    HasDerivAt (deriv (fun t => J (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t)))
      (inner Real (hilbertHessian J (activeAntisymmetricPoint A)
          (activeMomentRetractFirst O P.measure P.velocity 0))
          (activeMomentRetractFirst O P.measure P.velocity 0) +
       inner Real (hilbertGradient J (activeAntisymmetricPoint A))
          (activeMomentRetractSecond O P.measure P.velocity 0)) 0 ∧
    -(activeC2CurvatureConstant J R) * variationEnergy P ≤
      deriv (deriv (fun t => J (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t))) 0 := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  have hp (t : Real) := (activeMomentMapAlongRetract_variations O P.measure P.velocity P.tangent P.continuous_velocity t).1
  have hv := (activeMomentMapAlongRetract_variations O P.measure P.velocity P.tangent P.continuous_velocity 0).2
  have hz : activeMomentMapAlongRetract O P.measure P.velocity P.tangent 0 = activeAntisymmetricPoint A :=
    (activeMomentMapAlongRetract_zero O P).trans hbase
  have hchain := hilbert_second_chain J hJ hp hv
  have hlower := hilbert_second_chain_lower J hJ hp hv
  rw [hz] at hchain hlower
  refine ⟨hchain, ?_⟩
  have hs := active_c2_suprema_bounds J hJ R A hA
  have hj := spherical_active_retraction_moment_bounds O P
  rw [(activeMomentMapAlongRetract_variations O P.measure P.velocity P.tangent P.continuous_velocity 0).1.deriv,
    (activeMomentMapAlongRetract_second_derivative O P.measure P.velocity P.tangent P.continuous_velocity 0).deriv] at hj
  have hE : 0 ≤ variationEnergy P := by
    rw [← productTangentEnergy_eq_variationEnergy]
    exact productTangentEnergy_nonneg _ _
  have hC : 0 ≤ ∑ n ∈ O, (n : Real) ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hj1 := (sq_le_sq₀ (norm_nonneg (activeMomentRetractFirst O P.measure P.velocity 0))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hj.1
  rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt hE] at hj1
  have hb1 : ‖hilbertHessian J (activeAntisymmetricPoint A)‖ *
        ‖activeMomentRetractFirst O P.measure P.velocity 0‖ ^ 2 ≤
      activeHessianSup J R * ((∑ n ∈ O, (n : Real) ^ 2) * variationEnergy P) :=
    (mul_le_mul_of_nonneg_right hs.2.1 (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hj1 hs.2.2.2)
  have hb2 : ‖hilbertGradient J (activeAntisymmetricPoint A)‖ *
        ‖activeMomentRetractSecond O P.measure P.velocity 0‖ ≤
      activeGradientSup J R * (Real.sqrt (∑ n ∈ O, (n : Real) ^ 4) * variationEnergy P) :=
    (mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hj.2 hs.2.2.1)
  unfold activeC2CurvatureConstant
  nlinarith

/-- On the actual reflected branch, the required source base coordinate is derived. -/
theorem activeMomentMap_reflected_branch {d : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (P : SphericalVariation d)
    (hbranch : P.measure 1 = reflectedMeasure (P.measure 0)) :
    activeMomentMap O (P.measure 0) (P.measure 1) =
      activeAntisymmetricPoint (antisymmetricActiveMoment O (P.measure 0) (P.measure 1)) := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change symmetricActiveMoment O (P.measure 0) (P.measure 1) = 0
    apply Subtype.ext
    apply PiLp.ext
    intro n
    change symmetricMoment (P.measure 0) (P.measure 1) n.val = 0
    rw [hbranch]
    exact reflected_branch_symmetric_zero (P.measure 0) n.val (hO n.val n.property)
  · rfl

/-- The universal source active radius yields an actual retraction curvature bound
for any C2 active functional, without restricting the perturbation to the branch. -/
theorem spherical_retraction_c2_branch_curvature {d : Nat} (O : Finset Nat)
    (hO : ∀ n ∈ O, Odd n) (J : ActiveMomentCoordinates d O → Real) (hJ : ContDiff Real 2 J)
    (P : SphericalVariation d) (hbranch : P.measure 1 = reflectedMeasure (P.measure 0)) :
    -(activeC2CurvatureConstant J (Real.sqrt (O.card : Real))) * variationEnergy P ≤
      deriv (deriv (fun t => J (activeMomentMapAlongRetract O P.measure P.velocity P.tangent t))) 0 := by
  exact (spherical_retraction_c2_active_curvature O J hJ P (Real.sqrt (O.card : Real))
    (antisymmetricActiveMoment O (P.measure 0) (P.measure 1))
    (activeMomentMap_reflected_branch O hO P hbranch)
    (antisymmetricActiveMoment_norm_le O (P.measure 0) (P.measure 1))).2

end PaperFormalization.MatrixFactorization
