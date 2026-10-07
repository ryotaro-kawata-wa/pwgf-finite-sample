import PaperFormalization.Continuous.BlockOperator
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # Actual finite-configuration differentiation through averaged feature moments

The feature map takes values in an arbitrary real normed moment space; it can
later be instantiated by the manuscript's weighted feature map J_0, once its
primitive derivative has been proved. No infinite-series C2 result is assumed
to have been formalized here. The joint field derivative is a primitive input
on moment space times particle space, not an assumed configuration Jacobian.

The empirical field differentiates its averaged moment argument and therefore
has both diagonal and reciprocal-particle-count kernel blocks. A field with a
fixed population moment has only the diagonal configuration derivative. In
particular, the manuscript's full population-sampled Hessian must not be
identified with the Jacobian of the frozen-population field.
-/

open scoped BigOperators

namespace PaperFormalization.Manuscript

open Continuous

variable {ι E H : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual finite-configuration moment vector, with exact 1/N normalization. -/
noncomputable def empiricalMomentMap (φ : E → H) (X : PiLp 2 fun _ : ι => E) : H :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ j, φ (X j)

/-- The candidate moment derivative is explicitly constructed from coordinate derivatives. -/
noncomputable def empiricalMomentDerivative (dφ : ι → E →L[ℝ] H) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] H := by
  classical
  exact (Fintype.card ι : ℝ)⁻¹ •
    ∑ j, (dφ j).comp (PiLp.proj 2 (fun _ : ι => E) j)

/-- Applying the constructed moment derivative gives the averaged directional features. -/
theorem empiricalMomentDerivative_apply (dφ : ι → E →L[ℝ] H)
    (h : PiLp 2 fun _ : ι => E) :
    empiricalMomentDerivative dφ h = (Fintype.card ι : ℝ)⁻¹ • ∑ j, dφ j (h j) := by
  simp [empiricalMomentDerivative]

/-- Differentiating the actual averaged feature map produces its constructed derivative. -/
theorem hasFDerivAt_empiricalMomentMap (φ : E → H) (X : PiLp 2 fun _ : ι => E)
    (dφ : ι → E →L[ℝ] H) (hφ : ∀ j, HasFDerivAt φ (dφ j) (X j)) :
    HasFDerivAt (empiricalMomentMap φ) (empiricalMomentDerivative dφ) X := by
  classical
  have hj : ∀ j, HasFDerivAt (fun Y : PiLp 2 fun _ : ι => E => φ (Y j))
      ((dφ j).comp (PiLp.proj 2 (fun _ : ι => E) j)) X := fun j =>
    (hφ j).comp X (PiLp.proj 2 (fun _ : ι => E) j).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
  change HasFDerivAt ((Fintype.card ι : ℝ)⁻¹ •
    (fun Y : PiLp 2 fun _ : ι => E => ∑ j, φ (Y j)))
    ((Fintype.card ι : ℝ)⁻¹ • ∑ j, (dφ j).comp (PiLp.proj 2 (fun _ : ι => E) j)) X
  exact hsum.const_smul (Fintype.card ι : ℝ)⁻¹

/-- A joint derivative splits its moment and spatial directions by linearity. -/
theorem joint_field_derivative_split (D : (H × E) →L[ℝ] E) (u : H) (v : E) :
    D (u, v) = (D.comp (ContinuousLinearMap.inl ℝ H E)) u +
      (D.comp (ContinuousLinearMap.inr ℝ H E)) v := by
  change D (u, v) = D (u, 0) + D (0, v)
  rw [← map_add]
  simp

/-- The empirical configuration field evaluates the joint field at the
empirical moment of the same configuration. -/
noncomputable def empiricalConfigurationField (φ : E → H) (V : H × E → E)
    (X : PiLp 2 fun _ : ι => E) : PiLp 2 fun _ : ι => E :=
  WithLp.toLp 2 (fun i => V (empiricalMomentMap φ X, X i))

/-- Raw chain-rule derivative, constructed before identifying its block formula. -/
noncomputable def empiricalConfigurationDerivative (dφ : ι → E →L[ℝ] H)
    (DV : ι → (H × E) →L[ℝ] E) :
    (PiLp 2 fun _ : ι => E) →L[ℝ] PiLp 2 fun _ : ι => E :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (DV i).comp
      ((empiricalMomentDerivative dφ).prod (PiLp.proj 2 (fun _ : ι => E) i)))

/-- The configuration chain rule identifies the raw derivative of the actual field. -/
theorem hasFDerivAt_empiricalConfigurationField_raw (φ : E → H) (V : H × E → E)
    (X : PiLp 2 fun _ : ι => E) (dφ : ι → E →L[ℝ] H)
    (DV : ι → (H × E) →L[ℝ] E)
    (hφ : ∀ j, HasFDerivAt φ (dφ j) (X j))
    (hV : ∀ i, HasFDerivAt V (DV i) (empiricalMomentMap φ X, X i)) :
    HasFDerivAt (empiricalConfigurationField φ V) (empiricalConfigurationDerivative dφ DV) X := by
  have hmoment := hasFDerivAt_empiricalMomentMap φ X dφ hφ
  have hcoord : ∀ i, HasFDerivAt
      (fun Y : PiLp 2 fun _ : ι => E => V (empiricalMomentMap φ Y, Y i))
      ((DV i).comp ((empiricalMomentDerivative dφ).prod
        (PiLp.proj 2 (fun _ : ι => E) i))) X := fun i =>
    (hV i).comp X (hmoment.prodMk (PiLp.proj 2 (fun _ : ι => E) i).hasFDerivAt)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.hasFDerivAt).comp X (hasFDerivAt_pi.mpr hcoord)

/-- Algebraic identification of the derived Jacobian with its diagonal plus
1/N all-to-all blocks. No block Jacobian was an input to the chain rule. -/
theorem empiricalConfigurationDerivative_eq_sampledBlockOperator
    (dφ : ι → E →L[ℝ] H) (DV : ι → (H × E) →L[ℝ] E) :
    empiricalConfigurationDerivative dφ DV =
      sampledBlockOperator
        (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E))
        (fun i j => ((DV i).comp (ContinuousLinearMap.inl ℝ H E)).comp (dφ j)) := by
  ext h i
  change (DV i) (empiricalMomentDerivative dφ h, h i) = _
  rw [joint_field_derivative_split, sampledBlockOperator_apply, empiricalMomentDerivative_apply]
  simp only [map_smul, map_sum, ContinuousLinearMap.comp_apply]
  abel

/-- The actual empirical field derivative is the manuscript's diagonal plus
normalized measure-kernel structure, from primitive feature and joint-field derivatives. -/
theorem hasFDerivAt_empiricalConfigurationField (φ : E → H) (V : H × E → E)
    (X : PiLp 2 fun _ : ι => E) (dφ : ι → E →L[ℝ] H)
    (DV : ι → (H × E) →L[ℝ] E)
    (hφ : ∀ j, HasFDerivAt φ (dφ j) (X j))
    (hV : ∀ i, HasFDerivAt V (DV i) (empiricalMomentMap φ X, X i)) :
    HasFDerivAt (empiricalConfigurationField φ V)
      (sampledBlockOperator
        (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E))
        (fun i j => ((DV i).comp (ContinuousLinearMap.inl ℝ H E)).comp (dφ j))) X := by
  rw [← empiricalConfigurationDerivative_eq_sampledBlockOperator]
  exact hasFDerivAt_empiricalConfigurationField_raw φ V X dφ DV hφ hV

/-- The totalized fderiv agrees with the actual derived block operator. -/
theorem fderiv_empiricalConfigurationField (φ : E → H) (V : H × E → E)
    (X : PiLp 2 fun _ : ι => E) (dφ : ι → E →L[ℝ] H)
    (DV : ι → (H × E) →L[ℝ] E)
    (hφ : ∀ j, HasFDerivAt φ (dφ j) (X j))
    (hV : ∀ i, HasFDerivAt V (DV i) (empiricalMomentMap φ X, X i)) :
    fderiv ℝ (empiricalConfigurationField φ V) X =
      sampledBlockOperator
        (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E))
        (fun i j => ((DV i).comp (ContinuousLinearMap.inl ℝ H E)).comp (dφ j)) :=
  (hasFDerivAt_empiricalConfigurationField φ V X dφ DV hφ hV).fderiv

/-- Moving one particle differentiates the empirical moment by exactly
1/N times that particle's feature derivative. -/
theorem empiricalMomentDerivative_single [DecidableEq ι]
    (dφ : ι → E →L[ℝ] H) (j : ι) (v : E) :
    empiricalMomentDerivative dφ (PiLp.single 2 j v) =
      (Fintype.card ι : ℝ)⁻¹ • dφ j v := by
  rw [empiricalMomentDerivative_apply]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

/-- The actual block operator exposes its Kronecker-diagonal and normalized
kernel contributions on a single-particle perturbation. -/
theorem sampledBlockOperator_single_apply [DecidableEq ι]
    (D : ι → E →L[ℝ] E) (B : ι → ι → E →L[ℝ] E) (i j : ι) (v : E) :
    sampledBlockOperator D B (PiLp.single 2 j v) i =
      (if i = j then D i v else 0) + (Fintype.card ι : ℝ)⁻¹ • B i j v := by
  rw [sampledBlockOperator_apply]
  have hs : (∑ k, B i k ((PiLp.single 2 j v : PiLp 2 fun _ : ι => E) k)) = B i j v := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  rw [hs]
  by_cases hij : i = j <;> simp [hij]

/-- The derived configuration derivative has precisely the coordinate block
formula: spatial delta_ij plus the averaged moment-mediated derivative. -/
theorem fderiv_empiricalConfigurationField_single [DecidableEq ι]
    (φ : E → H) (V : H × E → E) (X : PiLp 2 fun _ : ι => E)
    (dφ : ι → E →L[ℝ] H) (DV : ι → (H × E) →L[ℝ] E)
    (hφ : ∀ j, HasFDerivAt φ (dφ j) (X j))
    (hV : ∀ i, HasFDerivAt V (DV i) (empiricalMomentMap φ X, X i))
    (i j : ι) (v : E) :
    (fderiv ℝ (empiricalConfigurationField φ V) X) (PiLp.single 2 j v) i =
      (if i = j then DV i (0, v) else 0) +
        (Fintype.card ι : ℝ)⁻¹ • DV i (dφ j v, 0) := by
  rw [fderiv_empiricalConfigurationField φ V X dφ DV hφ hV]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.inl_apply] using sampledBlockOperator_single_apply
      (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E))
      (fun i j => ((DV i).comp (ContinuousLinearMap.inl ℝ H E)).comp (dφ j)) i j v

/-- A fixed moment parameter models the population field at a fixed time.
It is not replaced by the empirical moment of the varied configuration. -/
noncomputable def frozenMomentConfigurationField (V : H × E → E) (theta : H)
    (X : PiLp 2 fun _ : ι => E) : PiLp 2 fun _ : ι => E :=
  WithLp.toLp 2 (fun i => V (theta, X i))

/-- A frozen population moment has zero moment variation: differentiating
its actual field yields only the spatial diagonal. -/
theorem hasFDerivAt_frozenMomentConfigurationField (V : H × E → E) (theta : H)
    (X : PiLp 2 fun _ : ι => E) (DV : ι → (H × E) →L[ℝ] E)
    (hV : ∀ i, HasFDerivAt V (DV i) (theta, X i)) :
    HasFDerivAt (frozenMomentConfigurationField V theta)
      (diagonalOperator (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E))) X := by
  have hcoord : ∀ i, HasFDerivAt
      (fun Y : PiLp 2 fun _ : ι => E => V (theta, Y i))
      ((DV i).comp ((0 : (PiLp 2 fun _ : ι => E) →L[ℝ] H).prod
        (PiLp.proj 2 (fun _ : ι => E) i))) X := fun i =>
    (hV i).comp X ((hasFDerivAt_const theta X).prodMk
      (PiLp.proj 2 (fun _ : ι => E) i).hasFDerivAt)
  have hraw := ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.hasFDerivAt).comp X (hasFDerivAt_pi.mpr hcoord)
  have heq :
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.pi fun i => (DV i).comp
          ((0 : (PiLp 2 fun _ : ι => E) →L[ℝ] H).prod
            (PiLp.proj 2 (fun _ : ι => E) i))) =
        diagonalOperator (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E)) := by
    ext h i
    rfl
  exact hraw.congr_fderiv heq

/-- The totalized derivative of the frozen field is its actual diagonal derivative. -/
theorem fderiv_frozenMomentConfigurationField (V : H × E → E) (theta : H)
    (X : PiLp 2 fun _ : ι => E) (DV : ι → (H × E) →L[ℝ] E)
    (hV : ∀ i, HasFDerivAt V (DV i) (theta, X i)) :
    fderiv ℝ (frozenMomentConfigurationField V theta) X =
      diagonalOperator (fun i => (DV i).comp (ContinuousLinearMap.inr ℝ H E)) :=
  (hasFDerivAt_frozenMomentConfigurationField V theta X DV hV).fderiv

end PaperFormalization.Manuscript
