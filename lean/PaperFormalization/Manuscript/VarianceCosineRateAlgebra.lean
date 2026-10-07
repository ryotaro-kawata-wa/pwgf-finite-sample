import PaperFormalization.Manuscript.VarianceCosineResponseEvent
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Finite-scale arithmetic for the growing-horizon application
M13v VERIFIED UNIT (full example application remains open). Here s=N^(-1/16), P=N^theta and T=s^(-2).
This is a deterministic adapter, NOT a source-model completion theorem.
Its residual and comparison premises still have to be discharged by the
existing M13t theorem and uniform residual asymptotics in the final wrapper.
All constants in this adapter are explicit; zero forcing is permitted.
-/
namespace PaperFormalization.Manuscript

/-- Raising a real power to an integer power, with a strictly positive base. -/
theorem varianceCosine_rpow_nat (n x : Real) (hn : 0 < n) (k : Nat) :
    (n^x)^k = n^(x*(k:Real)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,ih,<- Real.rpow_add hn]
    congr 1
    push_cast
    ring

/-- Exact printed exponents, not rounded numerical values. -/
theorem varianceCosine_rate_exponents (n theta : Real) (hn : 0 < n) :
    (n^(-(1/16:Real)))^3*(n^theta)^4 = n^(-(3/16:Real)+4*theta) ∧
    (n^(-(1/16:Real)))^8*(n^theta)^4 = n^(-(1/2:Real)+4*theta) ∧
    n^(-(1/16:Real))*(n^theta)^4 = n^(-(1/16:Real)+4*theta) := by
  constructor
  . rw [varianceCosine_rpow_nat n _ hn 3,varianceCosine_rpow_nat n _ hn 4,<- Real.rpow_add hn]
    congr 1; ring
  constructor
  . rw [varianceCosine_rpow_nat n _ hn 8,varianceCosine_rpow_nat n _ hn 4,<- Real.rpow_add hn]
    congr 1; ring
  . rw [varianceCosine_rpow_nat n _ hn 4,<- Real.rpow_add hn]
    congr 1; ring

/-- The three powers needed in the stability proof, in positive finite scales.
Bstar is the actual supremum when this lemma is used with the preceding
source-envelope bound; it is not redefined as its estimated upper bound. -/
theorem varianceCosine_stability_scale_algebra
    (s P C L delta S A J cD Bstar : Real)
    (hs : 0 < s) (hs1 : s <= 1) (hP : 1 <= P) (hC : 1 <= C) (hL : 0 <= L)
    (hd : 0 <= delta) (hS : 0 <= S) (hA : 0 <= A) (hJ : 0 <= J)
    (hcD : 0 <= cD) (hB : 0 <= Bstar)
    (hdU : delta <= C*s^8*P) (hSU : S <= C*s^4*P)
    (hAU : A <= C*P) (hJU : J <= C*P) (hcDU : cD <= C*P)
    (hBU : Bstar <= (delta+A*S)*L/s) :
    Bstar <= 2*C^2*L*s^3*P^2 ∧
    2*J*Bstar <= 4*C^3*L*s^3*P^3 ∧
    s⁻¹^2*(delta+cD*(2*J*Bstar)) <= (C+4*C^4*L)*s*P^4 := by
  have hP0 : 0 <= P := by linarith
  have hC0 : 0 <= C := by linarith
  have hs84 : s^8 <= s^4 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have hs61 : s^6 <= s := by simpa only [pow_one] using pow_le_pow_of_le_one hs.le hs1 (show 1 <= 6 by omega)
  have hP14 : P <= P^4 := by simpa only [pow_one] using pow_le_pow_right₀ hP (show 1 <= 4 by omega)
  have hd' : delta <= C^2*s^4*P^2 := by
    calc
      _ <= C*s^8*P := hdU
      _ <= C*s^4*P := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs84 hC0) hP0
      _ <= (C*C)*s^4*(P*P) := by
        have hc : C <= C*C := by nlinarith
        have hp : P <= P*P := by nlinarith
        gcongr
      _ = _ := by ring
  have hAS : A*S <= C^2*s^4*P^2 := by
    have h := mul_le_mul hAU hSU hS (mul_nonneg hC0 hP0)
    convert h using 1 <;> try rfl
    ring
  have hcoef : delta+A*S <= 2*C^2*s^4*P^2 := by linarith
  have hbnd : Bstar <= 2*C^2*L*s^3*P^2 := by
    calc
      _ <= (delta+A*S)*L/s := hBU
      _ <= (2*C^2*s^4*P^2)*L/s := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hL) hs.le
      _ = _ := by field_simp <;> ring
  have hrad : 2*J*Bstar <= 4*C^3*L*s^3*P^3 := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hJU (by norm_num : (0:Real)<=2)) hbnd hB (by positivity)
    convert h using 1 <;> try rfl
    ring
  refine ⟨hbnd,hrad,?_⟩
  have hrad0 : 0 <= 2*J*Bstar := by positivity
  have hdr : cD*(2*J*Bstar) <= 4*C^4*L*s^3*P^4 := by
    have h := mul_le_mul hcDU hrad hrad0 (mul_nonneg hC0 hP0)
    convert h using 1 <;> try rfl
    ring
  calc
    _ <= s⁻¹^2*(C*s^8*P+4*C^4*L*s^3*P^4) :=
      mul_le_mul_of_nonneg_left (add_le_add hdU hdr) (sq_nonneg _)
    _ = C*s^6*P+4*C^4*L*s*P^4 := by field_simp <;> ring
    _ <= C*s*P^4+4*C^4*L*s*P^4 := by gcongr
    _ = _ := by ring

/-- Uniform response substitution yields s^3=N^(-3/16). -/
theorem varianceCosine_uniform_rate_algebra
    (s P K L Cresp Jresp loss : Real) (hs : 0 < s) (hs1 : s <= 1)
    (hK : 0 <= K) (hL : 0 <= L) (hCr : 0 <= Cresp) (hJr : 0 <= Jresp)
    (hresp : Cresp+Jresp <= L/s)
    (hloss : loss <= K*P^4*(s^8*(1+Cresp)+s^4*Jresp)) :
    loss <= K*(1+2*L)*s^3*P^4 := by
  have hC : Cresp <= L/s := by linarith
  have hJ : Jresp <= L/s := by linarith
  have hs83 : s^8 <= s^3 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have hs73 : s^7 <= s^3 := pow_le_pow_of_le_one hs.le hs1 (by omega)
  have hbracket : s^8*(1+Cresp)+s^4*Jresp <= (1+2*L)*s^3 := by
    calc
      _ <= s^8*(1+L/s)+s^4*(L/s) := by gcongr
      _ = s^8+L*s^7+L*s^3 := by field_simp <;> ring
      _ <= s^3+L*s^3+L*s^3 := by gcongr
      _ = _ := by ring
  calc
    loss <= K*P^4*(s^8*(1+Cresp)+s^4*Jresp) := hloss
    _ <= K*P^4*((1+2*L)*s^3) := mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by ring

/-- Late response substitution yields s^8=N^(-1/2). -/
theorem varianceCosine_late_rate_algebra
    (s P K L Cresp Jresp loss : Real) (hK : 0 <= K)
    (hC : Cresp <= L) (hJ : Jresp <= L*s^4)
    (hloss : loss <= K*P^4*(s^8*(1+Cresp)+s^4*Jresp)) :
    loss <= K*(1+2*L)*s^8*P^4 := by
  have hbracket : s^8*(1+Cresp)+s^4*Jresp <= (1+2*L)*s^8 := by
    calc
      _ <= s^8*(1+L)+s^4*(L*s^4) := by gcongr
      _ = _ := by ring
  calc
    loss <= K*P^4*(s^8*(1+Cresp)+s^4*Jresp) := hloss
    _ <= K*P^4*((1+2*L)*s^8) := mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by ring
end PaperFormalization.Manuscript
