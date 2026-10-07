import PaperFormalization.MatrixFactorization.HermiteFeatures

/-! # MF04: derivatives of the original finite Hermite activation

The jets evaluate algebraic derivatives of Mathlib's probabilists' Hermite
polynomials, with the same sqrt(n!) normalization as MF01. The zeroth jet is
identified with the existing activation. Explicit finite coefficient bounds
will supply Gaussian domination for the actual spherical pushforward features.
No derivative, growth bound, or integration identity is a model assumption.
-/

open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def hermiteRealPolynomial (n : Nat) : Polynomial Real :=
  (Polynomial.hermite n).map (Int.castRingHom Real)

noncomputable def normalizedHermiteJet (k n : Nat) (x : Real) : Real :=
  ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).eval x /
    Real.sqrt (n.factorial : Real)

@[simp] theorem normalizedHermiteJet_zero (n : Nat) (x : Real) :
    normalizedHermiteJet 0 n x = normalizedHermite n x := by
  rw [normalizedHermite_eval]
  simp only [normalizedHermiteJet, Function.iterate_zero, id_eq,
    hermiteRealPolynomial, Polynomial.eval_map]

theorem normalizedHermiteJet_hasDerivAt (k n : Nat) (x : Real) :
    HasDerivAt (normalizedHermiteJet k n) (normalizedHermiteJet (k+1) n x) x := by
  have hd := (((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).hasDerivAt x).div_const
    (Real.sqrt (n.factorial : Real))
  apply hd.congr_deriv
  simp only [normalizedHermiteJet, Function.iterate_succ_apply']

theorem normalizedHermiteJet_continuous (k n : Nat) :
    Continuous (normalizedHermiteJet k n) := by
  exact continuous_iff_continuousAt.mpr fun x =>
    (normalizedHermiteJet_hasDerivAt k n x).continuousAt

noncomputable def finiteHermiteActivationJet {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (x : Real) : Weight h :=
  O.sum (fun n => normalizedHermiteJet k n x • a n)

@[simp] theorem finiteHermiteActivationJet_zero {h : Nat} (O : Finset Nat)
    (a : Nat → Weight h) (x : Real) :
    finiteHermiteActivationJet 0 O a x = finiteHermiteActivation O a x := by
  simp only [finiteHermiteActivationJet, normalizedHermiteJet_zero, finiteHermiteActivation]

theorem finiteHermiteActivationJet_hasDerivAt {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (x : Real) :
    HasDerivAt (finiteHermiteActivationJet k O a) (finiteHermiteActivationJet (k+1) O a x) x := by
  exact HasDerivAt.fun_sum (fun n _ => (normalizedHermiteJet_hasDerivAt k n x).smul_const (a n))

theorem finiteHermiteActivationJet_continuous {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) : Continuous (finiteHermiteActivationJet k O a) := by
  exact continuous_iff_continuousAt.mpr fun x =>
    (finiteHermiteActivationJet_hasDerivAt k O a x).continuousAt


/-- An explicit coefficient bound is used for Gaussian domination below. -/
noncomputable def polynomialCoefficientMass (P : Polynomial Real) : Real :=
  (Finset.range (P.natDegree+1)).sum (fun j => abs (P.coeff j))

theorem polynomialCoefficientMass_nonneg (P : Polynomial Real) :
    0 ≤ polynomialCoefficientMass P := by
  exact Finset.sum_nonneg (fun j _ => abs_nonneg _)

theorem polynomial_eval_growth (P : Polynomial Real) (M : Nat)
    (hM : P.natDegree ≤ M) (x : Real) :
    abs (P.eval x) ≤ polynomialCoefficientMass P * (1+abs x)^M := by
  have hp (j : Nat) (hj : j ∈ Finset.range (P.natDegree+1)) :
      abs x^j ≤ (1+abs x)^M := by
    have hjM : j ≤ M := (by have hh := Finset.mem_range.mp hj; omega : j ≤ P.natDegree).trans hM
    exact (pow_le_pow_left₀ (abs_nonneg x) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg x]) hjM)
  rw [Polynomial.eval_eq_sum_range]
  calc
    _ ≤ (Finset.range (P.natDegree+1)).sum (fun j => abs (P.coeff j*x^j)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (Finset.range (P.natDegree+1)).sum (fun j => abs (P.coeff j)*abs x^j) := by
      simp only [abs_mul, abs_pow]
    _ ≤ (Finset.range (P.natDegree+1)).sum (fun j => abs (P.coeff j)*(1+abs x)^M) := by
      exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hp j hj) (abs_nonneg _))
    _ = _ := (Finset.sum_mul _ _ _).symm

noncomputable def hermiteJetMass (k n : Nat) : Real :=
  polynomialCoefficientMass ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)) /
    Real.sqrt (n.factorial : Real)

noncomputable def hermiteJetOrder (k : Nat) (O : Finset Nat) : Nat :=
  O.sup (fun n => ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).natDegree)

noncomputable def activationJetMass {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) : Real := O.sum (fun n => hermiteJetMass k n * norm (a n))

theorem hermiteJetMass_nonneg (k n : Nat) : 0 ≤ hermiteJetMass k n :=
  div_nonneg (polynomialCoefficientMass_nonneg _) (hermite_normalizer_pos n).le

theorem activationJetMass_nonneg {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) : 0 ≤ activationJetMass k O a :=
  Finset.sum_nonneg (fun n _ => mul_nonneg (hermiteJetMass_nonneg k n) (norm_nonneg _))

theorem normalizedHermiteJet_growth (k n M : Nat)
    (hM : ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).natDegree ≤ M)
    (x : Real) :
    abs (normalizedHermiteJet k n x) ≤ hermiteJetMass k n * (1+abs x)^M := by
  unfold normalizedHermiteJet hermiteJetMass
  rw [abs_div, abs_of_pos (hermite_normalizer_pos n)]
  have hb := div_le_div_of_nonneg_right (polynomial_eval_growth _ M hM x)
    (hermite_normalizer_pos n).le
  simpa only [div_mul_eq_mul_div] using hb

theorem finiteHermiteActivationJet_growth {h : Nat} (k : Nat) (O : Finset Nat)
    (a : Nat → Weight h) (x : Real) :
    norm (finiteHermiteActivationJet k O a x) ≤
      activationJetMass k O a * (1+abs x)^(hermiteJetOrder k O) := by
  calc
    _ ≤ O.sum (fun n => norm (normalizedHermiteJet k n x • a n)) := norm_sum_le _ _
    _ ≤ O.sum (fun n => (hermiteJetMass k n * norm (a n))*(1+abs x)^(hermiteJetOrder k O)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs]
      have hnM : ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).natDegree ≤ hermiteJetOrder k O :=
        Finset.le_sup (f := fun n => ((Polynomial.derivative^[k]) (hermiteRealPolynomial n)).natDegree) hn
      have hb := mul_le_mul_of_nonneg_right
        (normalizedHermiteJet_growth k n _ hnM x) (norm_nonneg (a n))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hb
    _ = _ := (Finset.sum_mul _ _ _).symm

end PaperFormalization.MatrixFactorization
