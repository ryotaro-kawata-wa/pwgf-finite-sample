import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Four-factor Hölder estimates with the actual L4 norms

Two Hölder steps, with exponents (4,4,2) and (2,2,1), give the
integrability and exact product bound needed by the Gaussian fitting estimates.
The measure and vector-valued functions are arbitrary; finiteness of their
fourth moments is explicit and no model-specific inequality is assumed.
-/
open MeasureTheory
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Four L4 functions have an integrable product of norms, bounded by the
product of their actual real-valued L4 norms. -/
theorem four_norm_integrable_and_le {α E F G H : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] [NormedAddCommGroup H]
    {mu : Measure α} {f : α → E} {g : α → F} {h : α → G} {k : α → H}
    (hf : MemLp f 4 mu) (hg : MemLp g 4 mu) (hh : MemLp h 4 mu) (hk : MemLp k 4 mu) :
    Integrable (fun x => norm (f x)*norm (g x)*norm (h x)*norm (k x)) mu ∧
      (∫ x, norm (f x)*norm (g x)*norm (h x)*norm (k x) ∂mu) ≤
        lpNorm f 4 mu*lpNorm g 4 mu*lpNorm h 4 mu*lpNorm k 4 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  letI : ENNReal.HolderTriple 2 2 1 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  let A := fun x => norm (f x)*norm (g x)
  let B := fun x => norm (h x)*norm (k x)
  have hA : MemLp A 2 mu := hg.norm.mul' hf.norm
  have hB : MemLp B 2 mu := hk.norm.mul' hh.norm
  have hAB : MemLp (fun x => A x*B x) 1 mu := hB.mul' hA
  have hAe : eLpNorm A 2 mu ≤ eLpNorm f 4 mu*eLpNorm g 4 mu := by
    simpa only [A, smul_eq_mul, Pi.mul_def, eLpNorm_norm] using
      (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hg.1.norm hf.1.norm)
  have hBe : eLpNorm B 2 mu ≤ eLpNorm h 4 mu*eLpNorm k 4 mu := by
    simpa only [B, smul_eq_mul, Pi.mul_def, eLpNorm_norm] using
      (eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hk.1.norm hh.1.norm)
  have he : eLpNorm (fun x => A x*B x) 1 mu ≤
      (eLpNorm f 4 mu*eLpNorm g 4 mu)*(eLpNorm h 4 mu*eLpNorm k 4 mu) := by
    have hh : eLpNorm (fun x => A x*B x) 1 mu ≤ eLpNorm A 2 mu*eLpNorm B 2 mu := by
      simpa only [smul_eq_mul,Pi.mul_def] using
        (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hB.1 hA.1)
    exact hh.trans (mul_le_mul' hAe hBe)
  have hfin : (eLpNorm f 4 mu*eLpNorm g 4 mu)*(eLpNorm h 4 mu*eLpNorm k 4 mu) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top)
      (ENNReal.mul_ne_top hh.eLpNorm_ne_top hk.eLpNorm_ne_top)
  have hr := ENNReal.toReal_mono hfin he
  simp only [ENNReal.toReal_mul, toReal_eLpNorm hAB.1, toReal_eLpNorm hf.1,
    toReal_eLpNorm hg.1, toReal_eLpNorm hh.1, toReal_eLpNorm hk.1,
    lpNorm_one_eq_integral_norm hAB.1] at hr
  simp only [A,B,norm_mul,norm_norm,mul_assoc] at hr
  refine ⟨?_,by simpa only [mul_assoc] using hr⟩
  simpa only [A,B,mul_assoc] using (memLp_one_iff_integrable.mp hAB)

/-- A repeated L4 factor gives the squared factor needed for the exact
fitting-force estimate. No L2 coefficient substitute is used. -/
theorem integral_norm_sq_mul_norm_mul_norm_le_lpNorm_four {α E F G : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {mu : Measure α} {f : α → E} {g : α → F} {h : α → G}
    (hf : MemLp f 4 mu) (hg : MemLp g 4 mu) (hh : MemLp h 4 mu) :
    (∫ x, norm (f x)^2*norm (g x)*norm (h x) ∂mu) ≤
      lpNorm f 4 mu^2*lpNorm g 4 mu*lpNorm h 4 mu := by
  simpa only [pow_two] using (four_norm_integrable_and_le hf hf hg hh).2

end PaperFormalization.MatrixFactorization
