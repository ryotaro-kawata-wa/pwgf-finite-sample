import PaperFormalization.MatrixFactorization.ActiveMomentExpVariation

/-! # MF34: active Hilbert aggregation of the actual moment jets

The constants use the raw symmetric tensor Hilbert norms, with exact source
powers n^2 and n^4. No uniform coefficient weight replaces the active degrees.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Squared norm of the actual first active tensor derivative. -/
theorem rawActiveFirst_norm_sq_le {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    ‖rawActiveFirst O mu v t‖ ^ 2 ≤ (∑ n : O, (n.val : Real) ^ 2) * (∫ w, ‖v w‖ ^ 2 ∂mu) := by
  rw [activeMoment_norm_sq, rawActiveFirst_val O mu v hv hc t]
  have hE : 0 ≤ ∫ w, ‖v w‖ ^ 2 ∂mu := integral_nonneg (fun w => sq_nonneg _)
  calc
    (∑ n : O, ‖rawActiveTensorFirst O mu v t n‖ ^ 2) ≤
        ∑ n : O, (n.val : Real) ^ 2 * (∫ w, ‖v w‖ ^ 2 ∂mu) := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := rawMomentAlongExpFirst_norm_le (n := n.val) mu v hv hc t
      have hs := sq_le_sq₀ (norm_nonneg (rawMomentAlongExpFirst n.val mu v t))
        (mul_nonneg (Nat.cast_nonneg n.val) (Real.sqrt_nonneg _)) |>.mpr hb
      convert hs using 1 <;> first | rfl | simp only [mul_pow, Real.sq_sqrt hE]
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Squared norm of the actual second active tensor derivative. -/
theorem rawActiveSecond_norm_sq_le {d : Nat} (O : Finset Nat) (mu : Measure (UnitSphere d))
    [IsProbabilityMeasure mu] (v : UnitSphere d → Weight d)
    (hv : ∀ w, inner Real w.val (v w) = 0) (hc : Continuous v) (t : Real) :
    ‖rawActiveSecond O mu v t‖ ^ 2 ≤ (∑ n : O, (n.val : Real) ^ 4) * (∫ w, ‖v w‖ ^ 2 ∂mu) ^ 2 := by
  rw [activeMoment_norm_sq, rawActiveSecond_val O mu v hv hc t]
  have hE : 0 ≤ ∫ w, ‖v w‖ ^ 2 ∂mu := integral_nonneg (fun w => sq_nonneg _)
  calc
    (∑ n : O, ‖rawActiveTensorSecond O mu v t n‖ ^ 2) ≤
        ∑ n : O, (n.val : Real) ^ 4 * (∫ w, ‖v w‖ ^ 2 ∂mu) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hb := rawMomentAlongExpSecond_norm_le (n := n.val) mu v hv hc t
      have hs := sq_le_sq₀ (norm_nonneg (rawMomentAlongExpSecond n.val mu v t))
        (mul_nonneg (sq_nonneg _) hE) |>.mpr hb
      convert hs using 1 <;> first | rfl | ring
    _ = _ := (Finset.sum_mul _ _ _).symm

set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 800000 in
/-- Generic source coordinate calculus in the genuine Hilbert product. -/
theorem activeCoordinates_hasDerivAt {d : Nat} {O : Finset Nat}
    {X Y : Real → ActiveMomentSpace d O} {x y : ActiveMomentSpace d O} {t : Real}
    (hx : HasDerivAt X x t) (hy : HasDerivAt Y y t) :
    HasDerivAt (fun s => activeCoordinates (X s) (Y s)) (activeCoordinates x y) t := by
  have hp : HasDerivAt (fun s => ![(1 / 2 : Real) • (X s + Y s), (1 / 2 : Real) • (X s - Y s)])
      ![(1 / 2 : Real) • (x + y), (1 / 2 : Real) • (x - y)] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert (hx.add hy).const_smul (1 / 2 : Real) using 1 <;> rfl
    · convert (hx.sub hy).const_smul (1 / 2 : Real) using 1 <;> rfl
  letI : NormedSpace Real (Fin 2 → ActiveMomentSpace d O) := Pi.normedSpace
  let L : (Fin 2 → ActiveMomentSpace d O) →L[Real] ActiveMomentCoordinates d O :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 2 => ActiveMomentSpace d O)).symm.toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivAt (F := Fin 2 → ActiveMomentSpace d O)
    (E := ActiveMomentCoordinates d O) t hp
  convert h using 1 <;> rfl

end PaperFormalization.MatrixFactorization
