import PaperFormalization.MatrixFactorization.SphereMoments

/-! # MF01: the original finite normalized-Hermite activation

psi_n = He_n/sqrt(n!), using Mathlib's probabilists'
Hermite coefficients. This is not a replacement monomial activation. The
finite expansion is the stated source assumption; coefficient nonvanishing
is not needed for these lemmas. No Parseval/contraction identity is claimed.
-/

open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def normalizedHermite (n : Nat) (x : Real) : Real :=
  ((Finset.range (n+1)).sum (fun k => ((Polynomial.hermite n).coeff k : Real) * x^k)) /
    Real.sqrt (n.factorial : Real)

theorem normalizedHermite_eval (n : Nat) (x : Real) :
    normalizedHermite n x =
      (Polynomial.hermite n).eval₂ (Int.castRingHom Real) x / Real.sqrt (n.factorial : Real) := by
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_hermite]
  rfl

@[simp] theorem normalizedHermite_zero (x : Real) : normalizedHermite 0 x = 1 := by
  norm_num [normalizedHermite, Polynomial.hermite_zero]

@[simp] theorem normalizedHermite_one (x : Real) : normalizedHermite 1 x = x := by
  norm_num [normalizedHermite, Polynomial.hermite_one, Finset.sum_range_succ]

theorem hermite_normalizer_pos (n : Nat) : 0 < Real.sqrt (n.factorial : Real) := by
  apply Real.sqrt_pos.mpr
  exact_mod_cast Nat.factorial_pos n

theorem normalizedHermite_continuous (n : Nat) : Continuous (normalizedHermite n) := by
  unfold normalizedHermite
  fun_prop

/-- Parity is derived from the actual Hermite coefficients. -/
theorem normalizedHermite_odd (n : Nat) (hn : Odd n) (x : Real) :
    normalizedHermite n (-x) = -normalizedHermite n x := by
  have hterm (k : Nat) :
      ((Polynomial.hermite n).coeff k : Real)*(-x)^k =
        -(((Polynomial.hermite n).coeff k : Real)*x^k) := by
    rcases Nat.even_or_odd k with hk | hk
    . have hzero := Polynomial.coeff_hermite_of_odd_add (hn.add_even hk)
      simp [hzero]
    . rw [hk.neg_pow]
      ring
  unfold normalizedHermite
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, neg_div]

noncomputable def hermiteCoefficientMass (n : Nat) : Real :=
  (Finset.range (n+1)).sum (fun k => abs ((Polynomial.hermite n).coeff k : Real)) /
    Real.sqrt (n.factorial : Real)

theorem hermiteCoefficientMass_nonneg (n : Nat) : 0 <= hermiteCoefficientMass n := by
  unfold hermiteCoefficientMass
  positivity

/-- A finite polynomial bound whose constants depend only on activation data. -/
theorem normalizedHermite_growth (n M : Nat) (hn : n <= M) (x : Real) :
    abs (normalizedHermite n x) <= hermiteCoefficientMass n*(1+abs x)^M := by
  have hpow (k : Nat) (hk : k ∈ Finset.range (n+1)) :
      abs x^k <= (1+abs x)^M := by
    have hkM : k <= M := (by have hh := Finset.mem_range.mp hk; omega : k <= n).trans hn
    calc
      _ <= (1+abs x)^k := pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg x]) k
      _ <= _ := pow_le_pow_right₀ (by linarith [abs_nonneg x]) hkM
  have hs : abs ((Finset.range (n+1)).sum (fun k => ((Polynomial.hermite n).coeff k : Real)*x^k)) <=
      ((Finset.range (n+1)).sum (fun k => abs ((Polynomial.hermite n).coeff k : Real)))*(1+abs x)^M := by
    calc
      _ <= (Finset.range (n+1)).sum (fun k => abs (((Polynomial.hermite n).coeff k : Real)*x^k)) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = (Finset.range (n+1)).sum (fun k => abs ((Polynomial.hermite n).coeff k : Real)*abs x^k) := by
        simp only [abs_mul, abs_pow]
      _ <= (Finset.range (n+1)).sum (fun k => abs ((Polynomial.hermite n).coeff k : Real)*(1+abs x)^M) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hpow k hk) (abs_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  unfold normalizedHermite hermiteCoefficientMass
  rw [abs_div, abs_of_pos (hermite_normalizer_pos n)]
  have hh := div_le_div_of_nonneg_right hs (hermite_normalizer_pos n).le
  simpa only [div_mul_eq_mul_div] using hh

noncomputable def finiteHermiteActivation {h : Nat} (O : Finset Nat)
    (a : Nat -> Weight h) (x : Real) : Weight h :=
  O.sum (fun n => normalizedHermite n x • a n)

noncomputable def activationMass {h : Nat} (O : Finset Nat) (a : Nat -> Weight h) : Real :=
  O.sum (fun n => hermiteCoefficientMass n * norm (a n))

def activationOrder (O : Finset Nat) : Nat := O.sup id

theorem activationMass_nonneg {h : Nat} (O : Finset Nat) (a : Nat -> Weight h) :
    0 <= activationMass O a := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (hermiteCoefficientMass_nonneg n) (norm_nonneg _)

theorem finiteHermiteActivation_continuous {h : Nat} (O : Finset Nat) (a : Nat -> Weight h) :
    Continuous (finiteHermiteActivation O a) := by
  unfold finiteHermiteActivation
  exact continuous_finsetSum _ (fun n _ => (normalizedHermite_continuous n).smul continuous_const)

theorem finiteHermiteActivation_odd {h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n) (x : Real) :
    finiteHermiteActivation O a (-x) = -finiteHermiteActivation O a x := by
  unfold finiteHermiteActivation
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [normalizedHermite_odd n (hO n hn), neg_smul]

theorem finiteHermiteActivation_growth {h : Nat} (O : Finset Nat) (a : Nat -> Weight h) (x : Real) :
    norm (finiteHermiteActivation O a x) <= activationMass O a*(1+abs x)^(activationOrder O) := by
  calc
    _ <= O.sum (fun n => norm (normalizedHermite n x • a n)) := norm_sum_le _ _
    _ <= O.sum (fun n => (hermiteCoefficientMass n * norm (a n))*(1+abs x)^(activationOrder O)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs]
      have hnM : n <= activationOrder O := Finset.le_sup (f := id) hn
      have hh := mul_le_mul_of_nonneg_right (normalizedHermite_growth n _ hnM x) (norm_nonneg (a n))
      convert hh using 1
      ring
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The literal mean-field feature, integrating over the weight sphere. -/
noncomputable def meanFeature {d h : Nat} (sigma : Real -> Weight h)
    (mu : Measure (UnitSphere d)) (z : Weight d) : Weight h :=
  integral mu (fun w => sigma (inner Real w.val z))

theorem meanFeature_weight_integrable {d h : Nat} (sigma : Real -> Weight h)
    (hsigma : Continuous sigma) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu]
    (z : Weight d) : Integrable (fun w : UnitSphere d => sigma (inner Real w.val z)) mu :=
  sphere_integrable mu _ (hsigma.comp (by fun_prop))

theorem meanFeature_stronglyMeasurable {d h : Nat} (sigma : Real -> Weight h)
    (hsigma : Continuous sigma) (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] :
    StronglyMeasurable (meanFeature sigma mu) := by
  have hc : Continuous (fun p : Weight d × UnitSphere d => sigma (inner Real p.2.val p.1)) := by
    exact hsigma.comp (by fun_prop)
  exact hc.stronglyMeasurable.integral_prod_right

/-- Reflection of a genuine marginal, not an assumption about its finite moments. -/
theorem meanFeature_reflected {d h : Nat} (sigma : Real -> Weight h)
    (hsigma : Continuous sigma) (hodd : forall x, sigma (-x) = -sigma x)
    (mu : Measure (UnitSphere d)) [IsFiniteMeasure mu] (z : Weight d) :
    meanFeature sigma (reflectedMeasure mu) z = -meanFeature sigma mu z := by
  unfold meanFeature
  rw [integral_reflectedMeasure mu (fun w : UnitSphere d => sigma (inner Real w.val z))
    (hsigma.comp (by fun_prop))]
  simp only [reflect_val, inner_neg_left, hodd, integral_neg]

theorem meanFeature_antipodal {d h : Nat} (sigma : Real -> Weight h)
    (hsigma : Continuous sigma) (hodd : forall x, sigma (-x) = -sigma x)
    (a : UnitSphere d) (z : Weight d) :
    meanFeature sigma (antipodalMeasure a) z = 0 := by
  have he := meanFeature_reflected sigma hsigma hodd (antipodalMeasure a) z
  rw [reflectedMeasure_antipodal] at he
  apply PiLp.ext
  intro i
  have hi := congrArg (fun v : Weight h => v i) he
  simp only [PiLp.neg_apply] at hi
  change meanFeature sigma (antipodalMeasure a) z i = 0
  linarith

/-- Finite source Hermite data derive oddness and the antipodal zero feature. -/
theorem finiteHermite_mean_antipodal {d h : Nat} (O : Finset Nat) (coeff : Nat -> Weight h)
    (hO : forall n, n ∈ O -> Odd n) (a : UnitSphere d) (z : Weight d) :
    meanFeature (finiteHermiteActivation O coeff) (antipodalMeasure a) z = 0 :=
  meanFeature_antipodal _ (finiteHermiteActivation_continuous O coeff)
    (finiteHermiteActivation_odd O coeff hO) a z

/-- The envelope coefficients are independent of the marginal mu and of the input z. -/
theorem finiteHermite_mean_growth {d h : Nat} (O : Finset Nat) (a : Nat -> Weight h)
    (mu : Measure (UnitSphere d)) [IsProbabilityMeasure mu] (z : Weight d) :
    norm (meanFeature (finiteHermiteActivation O a) mu z) <=
      activationMass O a*(1+norm z)^(activationOrder O) := by
  let f := fun w : UnitSphere d => finiteHermiteActivation O a (inner Real w.val z)
  have hi : Integrable f mu := meanFeature_weight_integrable _
    (finiteHermiteActivation_continuous O a) mu z
  have hbound (w : UnitSphere d) : norm (f w) <= activationMass O a*(1+norm z)^(activationOrder O) := by
    have hw : norm w.val = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
    have hip : abs (inner Real w.val z) <= norm z := by
      simpa only [hw, one_mul] using abs_real_inner_le_norm w.val z
    exact (finiteHermiteActivation_growth O a _).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _)
        (activationMass_nonneg O a))
  calc
    _ <= integral mu (fun w => norm (f w)) := norm_integral_le_integral_norm _
    _ <= integral mu (fun _ : UnitSphere d => activationMass O a*(1+norm z)^(activationOrder O)) :=
      integral_mono hi.norm (integrable_const _) hbound
    _ = _ := by simp

end PaperFormalization.MatrixFactorization
