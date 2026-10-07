import PaperFormalization.Manuscript.SourceActualJump
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # Actual inverse of particleFlatten for constructing coupled updates

M13p verified unit (see CODEX_HANDOFF_M13P.md). The product index is (particle, coordinate).
No normalization is changed, and zero particle/spatial dimensions are permitted.
-/
open MeasureTheory
namespace PaperFormalization.Manuscript
variable {N d : ℕ}

/-- Inverse regrouping of the actual product-index population vector. -/
def sourceParticleUnflatten (v : EuclideanSpace ℝ (Fin N × Fin d)) :
    PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)) :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => v (i,j)))

@[simp] theorem particleFlatten_sourceParticleUnflatten
    (v : EuclideanSpace ℝ (Fin N × Fin d)) :
    particleFlatten (sourceParticleUnflatten v) = v := by
  ext i
  rfl

@[simp] theorem sourceParticleUnflatten_particleFlatten
    (X : PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d))) :
    sourceParticleUnflatten (particleFlatten X) = X := by
  ext i j
  rfl

/-- The regrouping equivalence preserves the actual Euclidean particle norm. -/
noncomputable def sourceParticleFlattenIsometry :
    (PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)))
      ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N × Fin d) := {
  toLinearEquiv := {
    toFun := particleFlatten
    invFun := sourceParticleUnflatten
    left_inv := sourceParticleUnflatten_particleFlatten
    right_inv := particleFlatten_sourceParticleUnflatten
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  norm_map' := particleFlatten_norm }

theorem sourceParticleFlatten_measurable :
    Measurable (particleFlatten :
      PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d)) ->
        EuclideanSpace ℝ (Fin N × Fin d)) :=
  sourceParticleFlattenIsometry.continuous.measurable

theorem sourceParticleUnflatten_measurable :
    Measurable (sourceParticleUnflatten : EuclideanSpace ℝ (Fin N × Fin d) ->
      PiLp 2 (fun _ : Fin N => EuclideanSpace ℝ (Fin d))) :=
  sourceParticleFlattenIsometry.symm.continuous.measurable

end PaperFormalization.Manuscript
