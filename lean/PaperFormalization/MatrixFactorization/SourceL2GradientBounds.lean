import PaperFormalization.MatrixFactorization.SphereL2FirstVariation
import PaperFormalization.MatrixFactorization.PrimalProductGradient

/-! # MF28: source L2 gradients enter the actual model estimates

The original full objective supplies the derivative identity as an L2
pairing. The existing cap-free speed bound and cap-local identification are
then applied to its constructed Borel representative. Neither a dual
potential nor a supportwise classical differential is introduced.
Execution and source-scope records are in `MF28_WORKLOG.md`.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- The L2 formulation feeds the previously verified actual-model estimates,
including the Hilbert norm energy bound and current-law AE field identity. -/
theorem source_l2_gradient_statewise {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu : Fin 2 → Measure (UnitSphere d)) (hmu : ∀ i, IsProbabilityMeasure (mu i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (g : ∀ i, sphereTangentL2 (mu i))
    (H : ∀ i, HasSphereL2FirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    (∀ i, ∀ᵐ w ∂mu i,
      norm (sphereL2Representative (g i) w) ≤ primalObjectiveSpeedBound d O a lambda p) ∧
    (∀ i, norm (g i)^2 ≤ (primalObjectiveSpeedBound d O a lambda p)^2) ∧
    (∀ r : Real, (∀ i, TwoCapClass pole r (mu i)) → ∀ i,
      sphereL2Representative (g i) =ᵐ[mu i]
        sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher teacher i) := by
  have hpv (i : Fin 2) : HasSphereFirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (sphereL2Representative (g i)) := by
    letI := hmu i
    exact (H i).to_primal
  have hb := source_primal_gradient_statewise O a pole lambda p hl hp mu hmu teacher
    (fun i => sphereL2Representative (g i)) hpv
  refine ⟨hb.1, ?_, hb.2.2⟩
  intro i
  simpa only [sphereL2Representative_energy] using hb.2.1 i

end PaperFormalization.MatrixFactorization
