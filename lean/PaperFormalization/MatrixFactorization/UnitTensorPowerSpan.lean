import PaperFormalization.MatrixFactorization.TensorPowerSeparation

/-! # MF40: unit tensor powers span each symmetric tensor block

A supplied sphere point handles degree zero, where an empty sphere could
otherwise invalidate the statement. It is already present as the target pole
in the source model. No condition on the active coefficients is required.
-/
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 800000

/-- Homogeneity uses the unweighted raw tensor power at every natural order. -/
theorem tensorPower_smul {d n : Nat} (c : Real) (w : Weight d) :
    tensorPower n (c • w) = c ^ n • tensorPower n w := by
  apply PiLp.ext
  intro I
  simp [tensorPower_apply, Finset.prod_mul_distrib]

@[simp] theorem tensorPower_zero_succ (d n : Nat) : tensorPower (n + 1) (0 : Weight d) = 0 := by
  apply PiLp.ext
  intro I
  simp [tensorPower_apply]

@[simp] theorem symmetricTensorPower_smul {d n : Nat} (c : Real) (w : Weight d) :
    symmetricTensorPower n (c • w) = c ^ n • symmetricTensorPower n w := by
  apply Subtype.ext
  exact tensorPower_smul c w

/-- The actual sphere's pure tensors span, with the degree-zero case kept explicit. -/
theorem symmetricUnitTensorPower_span {d : Nat} (pole : UnitSphere d) (n : Nat) :
    Submodule.span Real (Set.range (fun w : UnitSphere d => symmetricTensorPower n w.val)) = ⊤ := by
  apply top_le_iff.mp
  rw [← symmetricTensorPower_span d n]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  let K := Submodule.span Real (Set.range (fun u : UnitSphere d => symmetricTensorPower n u.val))
  change symmetricTensorPower n w ∈ K
  by_cases hn : n = 0
  · subst n
    have he : symmetricTensorPower 0 w = symmetricTensorPower 0 pole.val := by
      apply Subtype.ext
      apply PiLp.ext
      intro I
      simp [symmetricTensorPower, tensorPower_apply]
    rw [he]
    exact Submodule.subset_span ⟨pole, rfl⟩
  · by_cases hw : w = 0
    · subst w
      have he : symmetricTensorPower n (0 : Weight d) = 0 := by
        apply Subtype.ext
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => exact tensorPower_zero_succ d n
      rw [he]
      exact K.zero_mem
    · have hnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      let u : UnitSphere d := ⟨‖w‖⁻¹ • w, by
        change ‖‖w‖⁻¹ • w - 0‖ = 1
        rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
          inv_mul_cancel₀ hnorm]⟩
      have he : ‖w‖ • u.val = w := by
        change ‖w‖ • (‖w‖⁻¹ • w) = w
        rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
      rw [← he, symmetricTensorPower_smul]
      exact K.smul_mem _ (Submodule.subset_span ⟨u, rfl⟩)

/-- A linear map on symmetric tensors is determined by actual unit-sphere observations. -/
theorem symmetricTensor_linear_ext_on_units {d n : Nat} (pole : UnitSphere d)
    {F : Type*} [AddCommMonoid F] [Module Real F]
    (L M : SymmetricMomentTensor d n →ₗ[Real] F)
    (h : ∀ w : UnitSphere d, L (symmetricTensorPower n w.val) = M (symmetricTensorPower n w.val)) :
    L = M := by
  apply LinearMap.ext_on (symmetricUnitTensorPower_span pole n)
  rintro _ ⟨w, rfl⟩
  exact h w

end PaperFormalization.MatrixFactorization
