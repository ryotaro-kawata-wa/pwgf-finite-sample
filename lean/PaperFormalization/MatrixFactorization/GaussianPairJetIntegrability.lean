import PaperFormalization.MatrixFactorization.HermiteDerivatives
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Actual fourth moments for the Gaussian activation and spherical jets

The scalar Gaussian input and an independent scalar tangent input are retained
literally. Finite Hermite polynomial growth supplies every required finite
moment. The source first and second spherical jet expressions are proved in
L4, including the second jet's radial acceleration term.
-/
open MeasureTheory ProbabilityTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every positive natural moment of every actual finite Hermite jet is finite. -/
theorem finiteHermiteActivationJet_gaussian_memLp {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (n : Nat) (hn : n ≠ 0) :
    MemLp (finiteHermiteActivationJet k O a) (n : ENNReal) (gaussianReal 0 1) := by
  let C := activationJetMass k O a
  let M := hermiteJetOrder k O
  have hsm : AEStronglyMeasurable (finiteHermiteActivationJet k O a) (gaussianReal 0 1) :=
    (finiteHermiteActivationJet_continuous k O a).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hsm (by exact_mod_cast hn) (by simp)).mp
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  have hbase : MemLp (fun x : Real => (1 : Real)+norm x) ((M*n : Nat) : ENNReal)
      (gaussianReal 0 1) :=
    (memLp_const (1 : Real)).add
      (memLp_id_gaussianReal' (μ := (0 : Real)) (v := (1 : NNReal))
        ((M*n : Nat) : ENNReal) (by finiteness)).norm
  have hnorm (x : Real) : norm ((1 : Real)+norm x) = 1+abs x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs]
  have hdom : Integrable (fun x : Real => C^n*(1+abs x)^(M*n)) (gaussianReal 0 1) := by
    simpa only [hnorm] using hbase.integrable_norm_pow'.const_mul (C^n)
  apply hdom.mono' (hsm.norm.pow n)
  filter_upwards with x
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ (C*(1+abs x)^M)^n :=
      pow_le_pow_left₀ (norm_nonneg _) (finiteHermiteActivationJet_growth k O a x) n
    _ = _ := by rw [mul_pow, ← pow_mul]

/-- The source activation has an actual finite fourth moment under a scalar standard Gaussian. -/
theorem finiteHermiteActivation_gaussian_memLp_four {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) :
    MemLp (finiteHermiteActivation O a) 4 (gaussianReal 0 1) := by
  have he : finiteHermiteActivationJet 0 O a = finiteHermiteActivation O a :=
    funext (finiteHermiteActivationJet_zero O a)
  rw [← he]
  exact finiteHermiteActivationJet_gaussian_memLp 0 O a 4 (by norm_num)

/-- The actual first spherical jet has a fourth moment under the independent Gaussian pair. -/
theorem gaussianPair_firstJet_memLp_four {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) :
    MemLp (fun xy : Real × Real => xy.2 • finiteHermiteActivationJet 1 O a xy.1)
      4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  letI : ENNReal.HolderTriple 8 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hj := (finiteHermiteActivationJet_gaussian_memLp 1 O a 8 (by norm_num)).comp_fst (gaussianReal 0 1)
  have hx := (memLp_id_gaussianReal' (μ := (0 : Real)) (v := (1 : NNReal))
    8 (by norm_num)).comp_snd (gaussianReal 0 1)
  exact hj.smul hx

/-- The actual second spherical jet retains its radial acceleration term and
has a fourth moment under the same independent Gaussian pair. -/
theorem gaussianPair_secondJet_memLp_four {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) :
    MemLp (fun xy : Real × Real =>
      xy.2^2 • finiteHermiteActivationJet 2 O a xy.1 -
        xy.1 • finiteHermiteActivationJet 1 O a xy.1)
      4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  letI : ENNReal.HolderTriple 8 8 4 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  letI : ENNReal.HolderTriple 16 16 8 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add]⟩
  have hj2 := (finiteHermiteActivationJet_gaussian_memLp 2 O a 8 (by norm_num)).comp_fst (gaussianReal 0 1)
  have hy16 := (memLp_id_gaussianReal' (μ := (0 : Real)) (v := (1 : NNReal))
    16 (by norm_num)).comp_snd (gaussianReal 0 1)
  have hy2 : MemLp (fun xy : Real × Real => xy.2^2) 8
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simpa only [Pi.mul_def, id_eq, sq] using hy16.mul hy16
  have hfirst : MemLp (fun xy : Real × Real => xy.2^2 • finiteHermiteActivationJet 2 O a xy.1)
      4 ((gaussianReal 0 1).prod (gaussianReal 0 1)) := hj2.smul hy2
  have hj1 := (finiteHermiteActivationJet_gaussian_memLp 1 O a 8 (by norm_num)).comp_fst (gaussianReal 0 1)
  have hx8 := (memLp_id_gaussianReal' (μ := (0 : Real)) (v := (1 : NNReal))
    8 (by norm_num)).comp_fst (gaussianReal 0 1)
  exact hfirst.sub (hj1.smul hx8)

end PaperFormalization.MatrixFactorization
