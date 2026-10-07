import PaperFormalization.Manuscript.JumpForcing
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact source square-root forcing and finite-jump powers

These scalar substitutions consume the independently proved continuous and
covariance residual envelopes. They act on the actual sourceJumpForcing and
jumpAmplification definitions; eta remains the prescribed jump amplitude.
The time term is kept as B*T/N by allowing an arbitrary nonnegative S there.
-/
open scoped BigOperators
namespace PaperFormalization.Manuscript

/-- Taking the square root of the actual inverse-sqrt sampling rate produces
exactly the quarter power, without an asymptotic substitution. -/
theorem sqrt_inverse_sqrt_eq_quarter_power (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt ((Real.sqrt n)⁻¹) = n^(-1/4 : ℝ) := by
  rw [Real.sqrt_inv, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn,
    ← Real.rpow_neg hn]
  congr 1
  ring

/-- Exact root-rate substitution for the two residuals. S may be B*T or T;
its dependence is retained inside the square root. -/
theorem source_residual_square_root_rate
    (N : ℕ) (x theta S gamma gammaTilde Cg Ct : ℝ)
    (hN : 0 < N) (hx : 0 < x) (hS : 0 ≤ S) (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct)
    (hg : gamma ≤ Cg*x^theta*((Real.sqrt N)⁻¹+S/N))
    (ht : gammaTilde ≤ Ct*x^theta*(Real.sqrt N)⁻¹) :
    Real.sqrt gamma + Real.sqrt gammaTilde ≤
      (Real.sqrt Cg+Real.sqrt Ct)*x^(theta/2)*
        ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N)) := by
  have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs : 0 ≤ S/(N : ℝ) := by positivity
  have hsplit : Real.sqrt ((Real.sqrt N)⁻¹+S/N) ≤
      Real.sqrt ((Real.sqrt N)⁻¹)+Real.sqrt (S/N) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt (show 0 ≤ (Real.sqrt (N : ℝ))⁻¹ by positivity),
        Real.sq_sqrt hs,
        mul_nonneg (Real.sqrt_nonneg ((Real.sqrt (N : ℝ))⁻¹)) (Real.sqrt_nonneg (S/N))]
  rw [sqrt_inverse_sqrt_eq_quarter_power N hn] at hsplit
  have hfactor (C : ℝ) (hC : 0 ≤ C) :
      Real.sqrt (C*x^theta) = Real.sqrt C*x^(theta/2) := by
    rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (x^theta), ← Real.rpow_mul hx.le]
    congr 2
    ring
  have hg' : Real.sqrt gamma ≤ Real.sqrt Cg*x^(theta/2)*
      ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N)) := by
    calc
      _ ≤ Real.sqrt (Cg*x^theta*((Real.sqrt N)⁻¹+S/N)) := Real.sqrt_le_sqrt hg
      _ = Real.sqrt (Cg*x^theta)*Real.sqrt ((Real.sqrt N)⁻¹+S/N) :=
        Real.sqrt_mul (by positivity) _
      _ ≤ _ := by
        rw [hfactor Cg hCg]
        exact mul_le_mul_of_nonneg_left hsplit (by positivity)
  have ht' : Real.sqrt gammaTilde ≤ Real.sqrt Ct*x^(theta/2)*
      ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N)) := by
    calc
      _ ≤ Real.sqrt (Ct*x^theta*(Real.sqrt N)⁻¹) := Real.sqrt_le_sqrt ht
      _ = Real.sqrt Ct*x^(theta/2)*(N : ℝ)^(-1/4 : ℝ) := by
        rw [Real.sqrt_mul (show 0 ≤ Ct*x^theta by positivity), hfactor Ct hCt,
          sqrt_inverse_sqrt_eq_quarter_power N hn]
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg (S/N)]) (by positivity)
  linarith

/-- Actual source jump forcing has exponent 3theta/2 and the N^-1/4 rate.
No upper bound on the prescribed amplitude is needed for this pointwise form. -/
theorem sourceJumpForcing_rate
    (N : ℕ) (x theta S A Ca Cg Ct : ℝ) (eta gammaPre gammaTildePre : ℕ → ℝ) (i : ℕ)
    (hN : 0 < N) (hx : 0 < x) (hS : 0 ≤ S)
    (hCa : 0 ≤ Ca) (hCg : 0 ≤ Cg) (hCt : 0 ≤ Ct) (heta : 0 ≤ eta i)
    (hAb : A ≤ Ca*x^theta)
    (hg : gammaPre i ≤ Cg*x^theta*((Real.sqrt N)⁻¹+S/N))
    (ht : gammaTildePre i ≤ Ct*x^theta*(Real.sqrt N)⁻¹) :
    sourceJumpForcing A eta gammaPre gammaTildePre i ≤
      Ca*(Real.sqrt Cg+Real.sqrt Ct)*x^(3*theta/2)*
        ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N))*eta i := by
  have hb := source_residual_square_root_rate N x theta S (gammaPre i) (gammaTildePre i)
    Cg Ct hN hx hS hCg hCt hg ht
  unfold sourceJumpForcing sourceJumpError
  calc
    _ ≤ (Ca*x^theta)*eta i*((Real.sqrt Cg+Real.sqrt Ct)*x^(theta/2)*
        ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N))) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hAb heta) hb
        (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity)
    _ = Ca*(Real.sqrt Cg+Real.sqrt Ct)*(x^theta*x^(theta/2))*
        ((N : ℝ)^(-1/4 : ℝ)+Real.sqrt (S/N))*eta i := by ring
    _ = _ := by rw [← Real.rpow_add hx, show theta+theta/2=3*theta/2 by ring]

/-- The actual finite product retains the exact jump count J. Constants are
independent of J, while the displayed prefactor and exponent depend on J. -/
theorem source_jumpAmplification_rate
    (J : ℕ) (x theta A Ca C0 : ℝ) (eta : ℕ → ℝ)
    (hx : 1 ≤ x) (htheta : 0 ≤ theta) (hA : 0 ≤ A)
    (hCa : 0 ≤ Ca) (hAb : A ≤ Ca*x^theta)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0) :
    jumpAmplification (sourceJumpError A eta) J ≤
      (1+Ca*C0)^J * x^((J : ℝ)*theta) := by
  have hx0 : 0 < x := by linarith
  have hpow : 1 ≤ x^theta := Real.one_le_rpow hx htheta
  have hnode (i : ℕ) (hi : i ∈ Finset.range J) :
      1+sourceJumpError A eta i ≤ (1+Ca*C0)*x^theta := by
    have he := heta i (Finset.mem_range.mp hi)
    have hm := mul_le_mul hAb he.2 he.1 (by positivity : 0 ≤ Ca*x^theta)
    unfold sourceJumpError
    nlinarith
  calc
    _ ≤ ∏ _i ∈ Finset.range J, ((1+Ca*C0)*x^theta) :=
      Finset.prod_le_prod (fun i hi => by
        have he := (heta i (Finset.mem_range.mp hi)).1
        unfold sourceJumpError
        positivity) hnode
    _ = ((1+Ca*C0)*x^theta)^J := by simp
    _ = (1+Ca*C0)^J * (x^theta)^J := mul_pow _ _ _
    _ = _ := by
      rw [← Real.rpow_natCast (x^theta) J, ← Real.rpow_mul hx0.le]
      congr 2
      ring

/-- A fixed real upper bound L0 on the number of jumps gives exactly the
source exponent L0*theta, including a schedule with no jumps. -/
theorem source_jumpAmplification_bounded_count_rate
    (J : ℕ) (L0 x theta A Ca C0 : ℝ) (eta : ℕ → ℝ)
    (hJ : (J : ℝ) ≤ L0) (hx : 1 ≤ x) (htheta : 0 ≤ theta) (hA : 0 ≤ A)
    (hCa : 0 ≤ Ca) (hC0 : 0 ≤ C0) (hAb : A ≤ Ca*x^theta)
    (heta : ∀ i < J, 0 ≤ eta i ∧ eta i ≤ C0) :
    jumpAmplification (sourceJumpError A eta) J ≤
      (1+Ca*C0)^L0 * x^(L0*theta) := by
  have hb := source_jumpAmplification_rate J x theta A Ca C0 eta hx htheta hA hCa hAb heta
  have hbase : 1 ≤ 1+Ca*C0 := by nlinarith
  have hp : (1+Ca*C0)^J ≤ (1+Ca*C0)^L0 := by
    rw [← Real.rpow_natCast (1+Ca*C0) J]
    exact Real.rpow_le_rpow_of_exponent_le hbase hJ
  have hxpow : x^((J : ℝ)*theta) ≤ x^(L0*theta) :=
    Real.rpow_le_rpow_of_exponent_le hx (mul_le_mul_of_nonneg_right hJ htheta)
  exact hb.trans (mul_le_mul hp hxpow (by positivity) (by positivity))

end PaperFormalization.Manuscript
