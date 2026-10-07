import PaperFormalization.Manuscript.EmpiricalFieldDerivative
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Differentiating the actual moment-gradient field

For real Hilbert particle and moment spaces, the field is the negative adjoint
feature derivative applied to the moment gradient. Its joint derivative is
proved by the adjoint linear map and the evaluation product rule. The feature
first-derivative field and moment gradient have explicit primitive derivative
hypotheses. This file does not prove weighted infinite-feature C2 regularity,
or identify a particular infinite-feature realization with these spaces. The
final specialization derives the primitive inputs from local C2 regularity of
the actual feature map and scalar moment objective.

The positive spatial and integral Hessian blocks are constructed below; their
negatives are the actual field Jacobian blocks. Spatial Hessian symmetry is
only invoked explicitly when matching the source's direction order.
-/

namespace PaperFormalization.Manuscript

open Continuous

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Adjoint is a continuous real-linear map between operator spaces. -/
noncomputable def realAdjointLinear : (E →L[ℝ] H) →L[ℝ] (H →L[ℝ] E) :=
  (ContinuousLinearMap.adjoint : (E →L[ℝ] H) ≃ₗᵢ[ℝ] (H →L[ℝ] E)).toContinuousLinearEquiv.toContinuousLinearMap

/-- The source field with its sign: `-Dφ(x)* gradG(theta)`. -/
noncomputable def momentGradientField (dφ : E → E →L[ℝ] H) (gradG : H → H)
    (p : H × E) : E := -(dφ p.2).adjoint (gradG p.1)

/-- The positive spatial block obtained by differentiating the feature derivative. -/
noncomputable def momentSpatialHessian (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) :
    E →L[ℝ] E := (realAdjointLinear.comp ddφ).flip g

/-- The positive moment-mediated kernel block, with its two distinct point slots. -/
noncomputable def momentIntegralHessian (dφx dφy : E →L[ℝ] H)
    (HessG : H →L[ℝ] H) : E →L[ℝ] E := dφx.adjoint.comp (HessG.comp dφy)

/-- Joint field derivative, constructed from the primitive derivatives. -/
noncomputable def momentGradientFieldDerivative (dφx : E →L[ℝ] H)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) (HessG : H →L[ℝ] H) :
    (H × E) →L[ℝ] E :=
  -((dφx.adjoint.comp HessG).comp (ContinuousLinearMap.fst ℝ H E) +
    (momentSpatialHessian ddφ g).comp (ContinuousLinearMap.snd ℝ H E))

/-- Evaluation exposes exactly the moment and spatial directional terms. -/
theorem momentGradientFieldDerivative_apply (dφx : E →L[ℝ] H)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) (HessG : H →L[ℝ] H)
    (u : H) (v : E) :
    momentGradientFieldDerivative dφx ddφ g HessG (u, v) =
      -(dφx.adjoint (HessG u)) - (ddφ v).adjoint g := by
  simp [momentGradientFieldDerivative, momentSpatialHessian, realAdjointLinear, neg_add_rev,
    sub_eq_add_neg, add_comm]

/-- The adjoint/evaluation product rule derives the joint derivative of the
actual field, without assuming any joint field or configuration Jacobian. -/
theorem hasFDerivAt_momentGradientField
    (dφ : E → E →L[ℝ] H) (gradG : H → H) (theta : H) (x : E)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (HessG : H →L[ℝ] H)
    (hφ : HasFDerivAt dφ ddφ x) (hG : HasFDerivAt gradG HessG theta) :
    HasFDerivAt (momentGradientField dφ gradG)
      (momentGradientFieldDerivative (dφ x) ddφ (gradG theta) HessG) (theta, x) := by
  have ha : HasFDerivAt (fun p : H × E => (dφ p.2).adjoint)
      (realAdjointLinear.comp (ddφ.comp (ContinuousLinearMap.snd ℝ H E))) (theta, x) :=
    (realAdjointLinear (E := E) (H := H)).hasFDerivAt.comp (theta, x)
      (hφ.comp (theta, x) (ContinuousLinearMap.snd ℝ H E).hasFDerivAt)
  have hg : HasFDerivAt (fun p : H × E => gradG p.1)
      (HessG.comp (ContinuousLinearMap.fst ℝ H E)) (theta, x) :=
    hG.comp (theta, x) hasFDerivAt_fst
  have hraw := (ha.clm_apply hg).neg
  apply hraw.congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp [momentGradientFieldDerivative, momentSpatialHessian, realAdjointLinear]

/-- Restricting to the spatial slot gives the negative spatial Hessian. -/
theorem momentGradientFieldDerivative_spatial (dφx : E →L[ℝ] H)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) (HessG : H →L[ℝ] H) :
    (momentGradientFieldDerivative dφx ddφ g HessG).comp
      (ContinuousLinearMap.inr ℝ H E) = -momentSpatialHessian ddφ g := by
  ext v
  simp [momentGradientFieldDerivative]

/-- Restricting to the moment slot gives the negative adjoint-Hessian composition. -/
theorem momentGradientFieldDerivative_moment (dφx : E →L[ℝ] H)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) (HessG : H →L[ℝ] H) :
    (momentGradientFieldDerivative dφx ddφ g HessG).comp
      (ContinuousLinearMap.inl ℝ H E) = -(dφx.adjoint.comp HessG) := by
  ext u
  simp [momentGradientFieldDerivative]

/-- Composing the moment-slot derivative with the feature derivative at a
second point produces the negative two-point integral Hessian. -/
theorem momentGradientFieldDerivative_kernel (dφx dφy : E →L[ℝ] H)
    (ddφ : E →L[ℝ] (E →L[ℝ] H)) (g : H) (HessG : H →L[ℝ] H) :
    ((momentGradientFieldDerivative dφx ddφ g HessG).comp
      (ContinuousLinearMap.inl ℝ H E)).comp dφy =
        -momentIntegralHessian dφx dφy HessG := by
  ext v
  simp [momentGradientFieldDerivative, momentIntegralHessian]

/-- The gradient representation is the adjoint identity, with the field sign. -/
theorem inner_momentGradientField (dφ : E → E →L[ℝ] H) (gradG : H → H)
    (theta : H) (x v : E) :
    inner ℝ (momentGradientField dφ gradG (theta, x)) v =
      -inner ℝ (gradG theta) (dφ x v) := by
  simp [momentGradientField, ContinuousLinearMap.adjoint_inner_left]

/-- The positive spatial block pairing, with derivative direction first. -/
theorem inner_momentSpatialHessian (ddφ : E →L[ℝ] (E →L[ℝ] H))
    (g : H) (u v : E) :
    inner ℝ u (momentSpatialHessian ddφ g v) = inner ℝ g (ddφ v u) := by
  change inner ℝ u ((ddφ v).adjoint g) = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

/-- Source direction order follows when the feature second derivative is
symmetric; this symmetry is explicit rather than silently assumed. -/
theorem inner_momentSpatialHessian_of_symmetric (ddφ : E →L[ℝ] (E →L[ℝ] H))
    (hsymm : ∀ u v, ddφ u v = ddφ v u) (g : H) (u v : E) :
    inner ℝ u (momentSpatialHessian ddφ g v) = inner ℝ g (ddφ u v) := by
  rw [inner_momentSpatialHessian, hsymm]

/-- The positive integral block pairing is the moment Hessian evaluated on
feature directions at the two point slots. -/
theorem inner_momentIntegralHessian (dφx dφy : E →L[ℝ] H)
    (HessG : H →L[ℝ] H) (u v : E) :
    inner ℝ u (momentIntegralHessian dφx dφy HessG v) =
      inner ℝ (dφx u) (HessG (dφy v)) := by
  exact ContinuousLinearMap.adjoint_inner_right dφx u (HessG (dφy v))


/-- Riesz realization of the actual second Frechet derivative of a scalar objective. -/
noncomputable def momentObjectiveHessian (G : H → ℝ) (theta : H) : H →L[ℝ] H :=
  (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ G) theta)

/-- Local C2 regularity suffices to differentiate the actual gradient. No
smoothness outside a neighborhood of the specified moment is required. -/
theorem hasFDerivAt_gradient_of_contDiffAt_two (G : H → ℝ) (theta : H)
    (hG : ContDiffAt ℝ 2 G theta) :
    HasFDerivAt (gradient G) (momentObjectiveHessian G theta) theta := by
  have hd : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) theta) theta :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  exact (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp theta hd

/-- The constructed Riesz Hessian is the derivative of the actual gradient. -/
theorem fderiv_gradient_eq_momentObjectiveHessian (G : H → ℝ) (theta : H)
    (hG : ContDiffAt ℝ 2 G theta) :
    fderiv ℝ (gradient G) theta = momentObjectiveHessian G theta :=
  (hasFDerivAt_gradient_of_contDiffAt_two G theta hG).fderiv

/-- The actual `Dφ` and `gradient G` field has the derived joint derivative
under local C2 assumptions, rather than an arbitrary gradient primitive. -/
theorem hasFDerivAt_actualMomentGradientField (φ : E → H) (G : H → ℝ)
    (theta : H) (x : E) (hφ : ContDiffAt ℝ 2 φ x) (hG : ContDiffAt ℝ 2 G theta) :
    HasFDerivAt (momentGradientField (fderiv ℝ φ) (gradient G))
      (momentGradientFieldDerivative (fderiv ℝ φ x) (fderiv ℝ (fderiv ℝ φ) x)
        (gradient G theta) (momentObjectiveHessian G theta)) (theta, x) :=
  hasFDerivAt_momentGradientField (fderiv ℝ φ) (gradient G) theta x
    (fderiv ℝ (fderiv ℝ φ) x) (momentObjectiveHessian G theta)
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
    (hasFDerivAt_gradient_of_contDiffAt_two G theta hG)

/-- The exact source gradient representation for the actual scalar objective. -/
theorem inner_actualMomentGradientField (φ : E → H) (G : H → ℝ)
    (theta : H) (x v : E) :
    inner ℝ (momentGradientField (fderiv ℝ φ) (gradient G) (theta, x)) v =
      -fderiv ℝ G theta (fderiv ℝ φ x v) := by
  rw [inner_momentGradientField]
  simp only [gradient, InnerProductSpace.toDual_symm_apply]

/-- The exact source spatial Hessian representation; local C2 of the feature
map supplies the otherwise necessary interchange of the two directions. -/
theorem inner_actualMomentSpatialHessian (φ : E → H) (G : H → ℝ)
    (theta : H) (x u v : E) (hφ : ContDiffAt ℝ 2 φ x) :
    inner ℝ u (momentSpatialHessian (fderiv ℝ (fderiv ℝ φ) x) (gradient G theta) v) =
      fderiv ℝ G theta (fderiv ℝ (fderiv ℝ φ) x u v) := by
  rw [inner_momentSpatialHessian_of_symmetric _ (hφ.isSymmSndFDerivAt (by norm_num))]
  simp only [gradient, InnerProductSpace.toDual_symm_apply]

/-- The exact source integral Hessian representation; local C2 of G supplies
symmetry and the source order of its two feature directions. -/
theorem inner_actualMomentIntegralHessian (φ : E → H) (G : H → ℝ)
    (theta : H) (x y u v : E) (hG : ContDiffAt ℝ 2 G theta) :
    inner ℝ u (momentIntegralHessian (fderiv ℝ φ x) (fderiv ℝ φ y)
        (momentObjectiveHessian G theta) v) =
      fderiv ℝ (fderiv ℝ G) theta (fderiv ℝ φ x u) (fderiv ℝ φ y v) := by
  rw [inner_momentIntegralHessian, real_inner_comm]
  change inner ℝ ((InnerProductSpace.toDual ℝ H).symm
    (fderiv ℝ (fderiv ℝ G) theta (fderiv ℝ φ y v))) (fderiv ℝ φ x u) = _
  rw [InnerProductSpace.toDual_symm_apply]
  exact (hG.isSymmSndFDerivAt (by norm_num)) _ _

/-- Local C2 assumptions derive the actual finite empirical configuration
Jacobian with its negative spatial and exact 1/N integral Hessian blocks. -/
theorem hasFDerivAt_actualEmpiricalMomentGradientField {ι : Type*} [Fintype ι]
    (φ : E → H) (G : H → ℝ) (X : PiLp 2 fun _ : ι => E)
    (hφ : ∀ i, ContDiffAt ℝ 2 φ (X i))
    (hG : ContDiffAt ℝ 2 G (empiricalMomentMap φ X)) :
    HasFDerivAt (empiricalConfigurationField φ
        (momentGradientField (fderiv ℝ φ) (gradient G)))
      (-sampledBlockOperator
        (fun i => momentSpatialHessian (fderiv ℝ (fderiv ℝ φ) (X i))
          (gradient G (empiricalMomentMap φ X)))
        (fun i j => momentIntegralHessian (fderiv ℝ φ (X i)) (fderiv ℝ φ (X j))
          (momentObjectiveHessian G (empiricalMomentMap φ X)))) X := by
  let DV : ι → (H × E) →L[ℝ] E := fun i =>
    momentGradientFieldDerivative (fderiv ℝ φ (X i)) (fderiv ℝ (fderiv ℝ φ) (X i))
      (gradient G (empiricalMomentMap φ X)) (momentObjectiveHessian G (empiricalMomentMap φ X))
  have hv : ∀ i, HasFDerivAt (momentGradientField (fderiv ℝ φ) (gradient G))
      (DV i) (empiricalMomentMap φ X, X i) := fun i =>
    hasFDerivAt_actualMomentGradientField φ G (empiricalMomentMap φ X) (X i) (hφ i) hG
  have hd := hasFDerivAt_empiricalConfigurationField φ
    (momentGradientField (fderiv ℝ φ) (gradient G)) X (fun i => fderiv ℝ φ (X i)) DV
    (fun i => (hφ i).differentiableAt two_ne_zero |>.hasFDerivAt) hv
  have hneg : HasFDerivAt (empiricalConfigurationField φ
      (momentGradientField (fderiv ℝ φ) (gradient G)))
      (sampledBlockOperator
        (fun i => -momentSpatialHessian (fderiv ℝ (fderiv ℝ φ) (X i))
          (gradient G (empiricalMomentMap φ X)))
        (fun i j => -momentIntegralHessian (fderiv ℝ φ (X i)) (fderiv ℝ φ (X j))
          (momentObjectiveHessian G (empiricalMomentMap φ X)))) X := by
    simpa only [DV, momentGradientFieldDerivative_spatial, momentGradientFieldDerivative_kernel] using hd
  apply hneg.congr_fderiv
  ext v i
  simp [sampledBlockOperator_apply, neg_add_rev, add_comm]

end PaperFormalization.Manuscript
