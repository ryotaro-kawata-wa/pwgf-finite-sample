import PaperFormalization.MatrixFactorization.PrimalObjectiveGradient
import PaperFormalization.MatrixFactorization.SphericalObjectiveSymmetry
import PaperFormalization.MatrixFactorization.SphericalObjectiveGradientSymmetry

/-! # MF24: the two actual product factors, with no dual representation

Verification status and conditional scope: see `MF24_VALIDATION.md`. The second factor uses the already proved exact
Frobenius/metric exchange symmetry, not a presumed scalar-output symmetry.
The input is the source's full partial L2 first-variation identity at the
current state. No new trajectory, all-time cap, field speed, or dual-gradient
assumption is introduced. This is a STATEWISE theorem, not global WGF closure.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def sourcePartialObjective {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (teacher : Measure (UnitSphere d))
    (i : Fin 2) (nu : Measure (UnitSphere d)) : Real :=
  if i = 0 then modelObjective O a pole lambda p nu (mu 1) teacher teacher
  else modelObjective O a pole lambda p (mu 0) nu teacher teacher

/-- The second component reduces to the active-first functional by exact exchange. -/
theorem sourcePartialObjective_active_first {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (teacher : Measure (UnitSphere d))
    (i : Fin 2) (nu : Measure (UnitSphere d)) :
    sourcePartialObjective O a pole lambda p mu teacher i nu =
      partialObjectiveFunctional O a pole lambda p (mu i.rev) teacher teacher nu := by
  fin_cases i
  · simp [sourcePartialObjective, partialObjectiveFunctional]
  · simpa [sourcePartialObjective, partialObjectiveFunctional] using
      modelObjective_exchange O a pole lambda p nu (mu 0) teacher teacher

/-- The canonical field is also the same after switching which factor is active. -/
theorem sourceGradient_active_first {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (mu : Fin 2 → Measure (UnitSphere d)) (teacher : Measure (UnitSphere d))
    (i : Fin 2) (w : UnitSphere d) :
    sphericalObjectiveGradient O a pole lambda p (mu i) (mu i.rev) teacher teacher 0 w =
      sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher teacher i w := by
  fin_cases i
  · simp
  · simpa using sphericalObjectiveGradient_exchange O a pole lambda p
      (mu 0) (mu 1) teacher teacher 0 w

/-- Main statewise bridge from the original full first variations. The same
constant works for both factors, independently of the measures and cap radius.
The local identity is AE under each original current marginal, not volume. -/
theorem source_primal_gradient_statewise {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (mu : Fin 2 → Measure (UnitSphere d)) (hmu : ∀ i, IsProbabilityMeasure (mu i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (g : Fin 2 → UnitSphere d → Weight d)
    (H : ∀ i, HasSphereFirstVariation (mu i)
      (sourcePartialObjective O a pole lambda p mu teacher i) (g i)) :
    (∀ i, ∀ᵐ w ∂mu i, norm (g i w) ≤ primalObjectiveSpeedBound d O a lambda p) ∧
    (∀ i, (∫ w, norm (g i w)^2 ∂mu i) ≤ (primalObjectiveSpeedBound d O a lambda p)^2) ∧
    (∀ r : Real, (∀ i, TwoCapClass pole r (mu i)) → ∀ i,
      g i =ᵐ[mu i] sphericalObjectiveGradient O a pole lambda p (mu 0) (mu 1) teacher teacher i) := by
  have Ha (i : Fin 2) : HasSphereFirstVariation (mu i)
      (partialObjectiveFunctional O a pole lambda p (mu i.rev) teacher teacher) (g i) :=
    (H i).congr_function (sourcePartialObjective_active_first O a pole lambda p mu teacher i)
  have hb (i : Fin 2) : ∀ᵐ w ∂mu i,
      norm (g i w) ≤ primalObjectiveSpeedBound d O a lambda p := by
    letI := hmu i
    letI := hmu i.rev
    exact primalObjectiveGradient_norm_le O a pole lambda p hl hp (mu i) (mu i.rev) teacher teacher (g i) (Ha i)
  refine ⟨hb, ?_, ?_⟩
  · intro i
    letI := hmu i
    have hh := integral_mono_ae (H i).norm_sq_integrable
      (integrable_const ((primalObjectiveSpeedBound d O a lambda p)^2)) (by
        filter_upwards [hb i] with w hw
        exact pow_le_pow_left₀ (norm_nonneg _) hw 2)
    simpa using hh
  · intro r hc i
    letI := hmu i
    letI := hmu i.rev
    have he := cap_primalObjectiveGradient_eq_ae O a pole r lambda p hp
      (mu i) (mu i.rev) teacher teacher (hc i) (g i) (Ha i)
    filter_upwards [he] with w hw
    exact hw.trans (sourceGradient_active_first O a pole lambda p mu teacher i w)

end PaperFormalization.MatrixFactorization
