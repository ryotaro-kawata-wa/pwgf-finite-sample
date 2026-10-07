import PaperFormalization.MatrixFactorization.PrimalProductGradient
import Mathlib.MeasureTheory.Measure.Prod

/-! # MF24: current-law bounds, original labels, and the exact Fubini quantifiers

Verification status and conditional scope: see `MF24_VALIDATION.md`. The current probability law is a literal pushforward.
The source first-variation identity may hold only at almost every time. Joint
measurability of the PULLED field is an explicit analytic input to the Fubini
adapter, not inferred from separate measurability. Conclusions are AE-label /
AE-time statements, never a silently uncountable intersection of conull sets.
This file does not assert an absolutely continuous characteristic representation.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Transfer the actual statewise bound and local field identity to original labels. -/
theorem source_primal_gradient_pullback {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (initial : Fin 2 → Measure (UnitSphere d)) (hi : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → UnitSphere d → UnitSphere d) (hm : ∀ i, Measurable (Phi i))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (g : Fin 2 → UnitSphere d → Weight d)
    (H : ∀ i, HasSphereFirstVariation ((initial i).map (Phi i))
      (sourcePartialObjective O a pole lambda p (fun j => (initial j).map (Phi j)) teacher i) (g i)) :
    (∀ i, ∀ᵐ w ∂initial i,
      norm (g i (Phi i w)) ≤ primalObjectiveSpeedBound d O a lambda p) ∧
    (∀ r : Real, (∀ i, TwoCapClass pole r ((initial i).map (Phi i))) → ∀ i,
      ∀ᵐ w ∂initial i, g i (Phi i w) = sphericalObjectiveGradient O a pole lambda p
        ((initial 0).map (Phi 0)) ((initial 1).map (Phi 1)) teacher teacher i (Phi i w)) := by
  have hprob (i : Fin 2) : IsProbabilityMeasure ((initial i).map (Phi i)) := by
    letI := hi i
    exact Measure.isProbabilityMeasure_map (hm i).aemeasurable
  have hb := source_primal_gradient_statewise O a pole lambda p hl hp
    (fun i => (initial i).map (Phi i)) hprob teacher g H
  exact ⟨fun i => ae_of_ae_map (hm i).aemeasurable (hb.1 i),
    fun r hc i => ae_of_ae_map (hm i).aemeasurable (hb.2.2 r hc i)⟩

/-- Fubini with its actual joint-measurability condition. Time may already be
restricted to an interval by choosing eta; the original law is not changed. -/
theorem ae_label_ae_time_bound_of_statewise {A : Type*} [MeasurableSpace A]
    (eta : Measure A) [SFinite eta] {d : Nat}
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu]
    (Phi : A → UnitSphere d → UnitSphere d) (hPhi : ∀ t, Measurable (Phi t))
    (g : A → UnitSphere d → Weight d) (C : Real)
    (hgm : Measurable (fun tw : A × UnitSphere d => g tw.1 (Phi tw.1 tw.2)))
    (hb : ∀ᵐ t ∂eta, ∀ᵐ w ∂mu.map (Phi t), norm (g t w) ≤ C) :
    ∀ᵐ w ∂mu, ∀ᵐ t ∂eta, norm (g t (Phi t w)) ≤ C := by
  have ht : ∀ᵐ t ∂eta, ∀ᵐ w ∂mu, norm (g t (Phi t w)) ≤ C := by
    filter_upwards [hb] with t ht
    exact ae_of_ae_map (hPhi t).aemeasurable ht
  exact (Measure.ae_ae_comm (μ := eta) (ν := mu)
    (p := fun t w => norm (g t (Phi t w)) ≤ C)
    (measurableSet_le hgm.norm measurable_const)).mp ht

/-- The original FULL objective identities supply the bound before the time /
label exchange. No separate regularizer gradient or speed estimate is an input. -/
theorem source_primal_gradient_time_label_bound {A : Type*} [MeasurableSpace A]
    (eta : Measure A) [SFinite eta] {d h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (pole : UnitSphere d) (lambda p : Real)
    (hl : 0 ≤ lambda) (hp : 2 < p)
    (initial : Fin 2 → Measure (UnitSphere d)) (hi : ∀ i, IsProbabilityMeasure (initial i))
    (Phi : Fin 2 → A → UnitSphere d → UnitSphere d)
    (hPhi : ∀ i t, Measurable (Phi i t))
    (teacher : Measure (UnitSphere d)) [IsProbabilityMeasure teacher]
    (g : Fin 2 → A → UnitSphere d → Weight d)
    (hgm : ∀ i, Measurable (fun tw : A × UnitSphere d => g i tw.1 (Phi i tw.1 tw.2)))
    (H : ∀ᵐ t ∂eta, ∀ i, HasSphereFirstVariation ((initial i).map (Phi i t))
      (sourcePartialObjective O a pole lambda p (fun j => (initial j).map (Phi j t)) teacher i) (g i t)) :
    ∀ i, ∀ᵐ w ∂initial i, ∀ᵐ t ∂eta,
      norm (g i t (Phi i t w)) ≤ primalObjectiveSpeedBound d O a lambda p := by
  intro i
  letI := hi i
  apply ae_label_ae_time_bound_of_statewise eta (initial i) (Phi i) (hPhi i) (g i) _ (hgm i)
  filter_upwards [H] with t ht
  have hprob (j : Fin 2) : IsProbabilityMeasure ((initial j).map (Phi j t)) := by
    letI := hi j
    exact Measure.isProbabilityMeasure_map (hPhi j t).aemeasurable
  exact (source_primal_gradient_statewise O a pole lambda p hl hp
    (fun j => (initial j).map (Phi j t)) hprob teacher (fun j => g j t) ht).1 i

end PaperFormalization.MatrixFactorization
