import PaperFormalization.MatrixFactorization.ActiveMomentMapJets

/-! # MF34: source degree constants for actual active moment derivatives

These estimates are on the true symmetric tensor Hilbert product, with both
components present for arbitrary continuous tangent perturbations. They do not
assume that a perturbation remains on the antisymmetric branch.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000

noncomputable def productTangentEnergy {d : Nat} (mu : Fin 2 → Measure (UnitSphere d))
    (v : Fin 2 → UnitSphere d → Weight d) : Real :=
  (∫ w, ‖v 0 w‖ ^ 2 ∂mu 0) + (∫ w, ‖v 1 w‖ ^ 2 ∂mu 1)

theorem productTangentEnergy_nonneg {d : Nat} (mu : Fin 2 → Measure (UnitSphere d))
    (v : Fin 2 → UnitSphere d → Weight d) : 0 ≤ productTangentEnergy mu v :=
  add_nonneg (integral_nonneg (fun w => sq_nonneg _)) (integral_nonneg (fun w => sq_nonneg _))

/-- The source first-jet coefficient comes from the exact factor-1/2 identity. -/
theorem activeMomentMapFirst_norm_sq_le {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsProbabilityMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    ‖activeMomentMapFirst O mu v t‖ ^ 2 ≤
      (∑ n : O, (n.val : Real) ^ 2) * productTangentEnergy mu v := by
  rw [activeMomentMapFirst, activeCoordinates_norm_sq]
  have h0 := rawActiveFirst_norm_sq_le O (mu 0) (v 0) (hv 0) (hc 0) t
  have h1 := rawActiveFirst_norm_sq_le O (mu 1) (v 1) (hv 1) (hc 1) t
  have hC : 0 ≤ ∑ n : O, (n.val : Real) ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hE := productTangentEnergy_nonneg mu v
  have hCE := mul_nonneg hC hE
  unfold productTangentEnergy at *
  nlinarith

/-- Source acceleration coefficient; both original laws contribute their energy. -/
theorem activeMomentMapSecond_norm_sq_le {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsProbabilityMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    ‖activeMomentMapSecond O mu v t‖ ^ 2 ≤
      (∑ n : O, (n.val : Real) ^ 4) * (productTangentEnergy mu v) ^ 2 := by
  rw [activeMomentMapSecond, activeCoordinates_norm_sq]
  have h0 := rawActiveSecond_norm_sq_le O (mu 0) (v 0) (hv 0) (hc 0) t
  have h1 := rawActiveSecond_norm_sq_le O (mu 1) (v 1) (hv 1) (hc 1) t
  have hC : 0 ≤ ∑ n : O, (n.val : Real) ^ 4 := Finset.sum_nonneg (fun n _ => by positivity)
  have hE0 : 0 ≤ ∫ w, ‖v 0 w‖ ^ 2 ∂mu 0 := integral_nonneg (fun w => sq_nonneg _)
  have hE1 : 0 ≤ ∫ w, ‖v 1 w‖ ^ 2 ∂mu 1 := integral_nonneg (fun w => sq_nonneg _)
  have hCE0 := mul_nonneg hC (sq_nonneg (∫ w, ‖v 0 w‖ ^ 2 ∂mu 0))
  have hCE1 := mul_nonneg hC (sq_nonneg (∫ w, ‖v 1 w‖ ^ 2 ∂mu 1))
  have hcross := mul_nonneg hC (mul_nonneg hE0 hE1)
  unfold productTangentEnergy
  nlinarith

/-- Both printed moment-coordinate estimates for the actual EXP-pushed laws. -/
theorem activeMomentMapAlongExp_derivative_bounds {d : Nat} (O : Finset Nat)
    (mu : Fin 2 → Measure (UnitSphere d)) [∀ i, IsProbabilityMeasure (mu i)]
    (v : Fin 2 → UnitSphere d → Weight d) (hv : ∀ i w, inner Real w.val (v i w) = 0)
    (hc : ∀ i, Continuous (v i)) (t : Real) :
    (∀ i, Integrable (fun w => ‖v i w‖ ^ 2) (mu i)) ∧
    ‖deriv (activeMomentMapAlongExp O mu v hv) t‖ ≤
      Real.sqrt (∑ n : O, (n.val : Real) ^ 2) * Real.sqrt (productTangentEnergy mu v) ∧
    ‖deriv (deriv (activeMomentMapAlongExp O mu v hv)) t‖ ≤
      Real.sqrt (∑ n : O, (n.val : Real) ^ 4) * productTangentEnergy mu v := by
  letI : NormedSpace Real (ActiveMomentCoordinates d O) := PiLp.normedSpace 2 Real _
  refine ⟨fun i => sphere_integrable (mu i) _ ((hc i).norm.pow 2), ?_, ?_⟩
  · rw [(activeMomentMapAlongExp_variations O mu v hv hc t).1.deriv]
    have hC : 0 ≤ ∑ n : O, (n.val : Real) ^ 2 := Finset.sum_nonneg (fun n _ => sq_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hC, Real.sq_sqrt (productTangentEnergy_nonneg mu v)]
    exact activeMomentMapFirst_norm_sq_le O mu v hv hc t
  · rw [(activeMomentMapAlongExp_second_derivative O mu v hv hc t).deriv]
    have hC : 0 ≤ ∑ n : O, (n.val : Real) ^ 4 := Finset.sum_nonneg (fun n _ => by positivity)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (productTangentEnergy_nonneg mu v))).mp
    rw [mul_pow, Real.sq_sqrt hC]
    exact activeMomentMapSecond_norm_sq_le O mu v hv hc t

end PaperFormalization.MatrixFactorization
