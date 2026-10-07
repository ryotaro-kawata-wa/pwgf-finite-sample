import PaperFormalization.MatrixFactorization.ScalarCapBarrier

/-! # MF15: integrate the scalar power dissipation inequality

The exponent alpha is any positive real, not an integer.
Inverse powers are used only on a segment whose terminal value is positive;
nonincrease then supplies positivity on that whole segment. Zero initial data
and zero hitting are treated without division. The result is an adapter for
MF14's actual transport derivative, not an extra trajectory assumption.
-/
open Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

noncomputable def powerDecayProfile (lambda alpha z0 t : Real) : Real :=
  z0 / (1 + lambda*alpha*z0^alpha*t)^(1/alpha)

@[simp] theorem powerDecayProfile_zero_initial (lambda alpha t : Real) :
    powerDecayProfile lambda alpha 0 t = 0 := by simp [powerDecayProfile]

@[simp] theorem powerDecayProfile_initial (lambda alpha z0 : Real) :
    powerDecayProfile lambda alpha z0 0 = z0 := by simp [powerDecayProfile]

theorem powerDecayProfile_nonneg {lambda alpha z0 t : Real}
    (hl : 0 ≤ lambda) (ha : 0 < alpha) (hz : 0 ≤ z0) (ht : 0 ≤ t) :
    0 ≤ powerDecayProfile lambda alpha z0 t := by
  unfold powerDecayProfile
  exact div_nonneg hz (Real.rpow_nonneg (by positivity) _)

theorem powerDecayProfile_le_initial {lambda alpha z0 t : Real}
    (hl : 0 ≤ lambda) (ha : 0 < alpha) (hz : 0 ≤ z0) (ht : 0 ≤ t) :
    powerDecayProfile lambda alpha z0 t ≤ z0 := by
  have hm : 0 ≤ lambda*alpha*z0^alpha*t := by positivity
  have hbase : 1 ≤ 1 + lambda*alpha*z0^alpha*t := by linarith
  have hden : 1 ≤ (1 + lambda*alpha*z0^alpha*t)^(1/alpha) :=
    Real.one_le_rpow hbase (by positivity)
  exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mpr
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hden hz)

/-- Algebraic equivalence to the integrated negative-power formula, at positive z0. -/
theorem powerDecayProfile_eq_inverse_power {lambda alpha z0 t : Real}
    (hl : 0 ≤ lambda) (ha : 0 < alpha) (hz : 0 < z0) (ht : 0 ≤ t) :
    powerDecayProfile lambda alpha z0 t =
      (z0^(-alpha) + lambda*alpha*t)^(-(1/alpha)) := by
  have hden : 0 < 1 + lambda*alpha*z0^alpha*t := by positivity
  have hinv : z0^(-alpha)*z0^alpha = 1 := by
    rw [← Real.rpow_add hz]
    simp
  have hfactor : z0^(-alpha) + lambda*alpha*t =
      z0^(-alpha)*(1 + lambda*alpha*z0^alpha*t) := by
    calc
      _ = z0^(-alpha) + lambda*alpha*t*(z0^(-alpha)*z0^alpha) := by rw [hinv]; ring
      _ = _ := by ring
  rw [hfactor, Real.mul_rpow (Real.rpow_nonneg hz.le _) hden.le,
    ← Real.rpow_mul hz.le]
  have hexp : (-alpha)*(-(1/alpha)) = 1 := by field_simp [ne_of_gt ha]
  rw [hexp, Real.rpow_one, Real.rpow_neg hden.le]
  simp only [powerDecayProfile,div_eq_mul_inv]

/-- Exact integrated estimate from a nonnegative scalar differential inequality.
Only interior-time differentiability is used. No positivity-at-all-times
hypothesis or no-hitting premise is required. -/
theorem scalar_power_decay {f : Real → Real} {T lambda alpha : Real}
    (hT : 0 ≤ T) (hl : 0 ≤ lambda) (ha : 0 < alpha)
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hinequality : ∀ t ∈ Ioo 0 T,
      deriv f t ≤ -lambda*(f t)^(alpha+1)) :
    AntitoneOn f (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, f t ≤ powerDecayProfile lambda alpha (f 0) t := by
  have hanti : AntitoneOn f (Icc 0 T) :=
    scalar_antitone_on_closed_interval hc hd (fun t ht =>
      (hinequality t ht).trans (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hl) (Real.rpow_nonneg (hpos t ⟨ht.1.le,ht.2.le⟩) _)))
  refine ⟨hanti, ?_⟩
  intro t ht
  by_cases hzero : f t = 0
  · rw [hzero]
    exact powerDecayProfile_nonneg hl ha (hpos 0 ⟨le_rfl,hT⟩) ht.1
  have htpos : 0 < f t := lt_of_le_of_ne (hpos t ht) (Ne.symm hzero)
  have hsegment : ∀ s ∈ Icc 0 t, 0 < f s := by
    intro s hs
    exact htpos.trans_le (hanti ⟨hs.1,hs.2.trans ht.2⟩ ht hs.2)
  have hz0 := hsegment 0 ⟨le_rfl,ht.1⟩
  let G : Real → Real := fun s => (f s)^(-alpha) - lambda*alpha*s
  have hGcont : ContinuousOn G (Icc 0 t) := by
    apply ContinuousOn.sub
    · exact (hc.mono (Icc_subset_Icc le_rfl ht.2)).rpow_const
        (fun s hs => Or.inl (ne_of_gt (hsegment s hs)))
    · fun_prop
  have hGder : ∀ s ∈ Ioo 0 t,
      HasDerivAt G
        ((-alpha)*(f s)^(-alpha-1)*deriv f s - lambda*alpha) s := by
    intro s hs
    have hh := ((hd s ⟨hs.1,hs.2.trans_le ht.2⟩).hasDerivAt.rpow_const
      (p := -alpha) (Or.inl (ne_of_gt (hsegment s ⟨hs.1.le,hs.2.le⟩)))).sub
        ((hasDerivAt_id s).const_mul (lambda*alpha))
    exact hh.congr_deriv (by ring)
  have hGnonneg : ∀ s ∈ Ioo 0 t, 0 ≤ deriv G s := by
    intro s hs
    rw [(hGder s hs).deriv]
    have hfs := hsegment s ⟨hs.1.le,hs.2.le⟩
    have hcoef : (-alpha)*(f s)^(-alpha-1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (Real.rpow_nonneg hfs.le _)
    have hmul := mul_le_mul_of_nonpos_left (hinequality s ⟨hs.1,hs.2.trans_le ht.2⟩) hcoef
    have hcancel : (f s)^(-alpha-1)*(f s)^(alpha+1) = 1 := by
      rw [← Real.rpow_add hfs]
      have he : -alpha-1+(alpha+1) = 0 := by ring
      rw [he, Real.rpow_zero]
    have he : ((-alpha)*(f s)^(-alpha-1))*(-lambda*(f s)^(alpha+1)) = lambda*alpha := by
      calc
        _ = lambda*alpha*((f s)^(-alpha-1)*(f s)^(alpha+1)) := by ring
        _ = _ := by rw [hcancel]; ring
    rw [he] at hmul
    linarith
  have hGmono : MonotoneOn G (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hGcont
    · rw [interior_Icc]
      exact fun s hs => (hGder s hs).differentiableAt.differentiableWithinAt
    · simpa only [interior_Icc] using hGnonneg
  have hbound : (f 0)^(-alpha)+lambda*alpha*t ≤ (f t)^(-alpha) := by
    have hh := hGmono ⟨le_rfl,ht.1⟩ ⟨ht.1,le_rfl⟩ ht.1
    dsimp [G] at hh
    linarith
  have hbase : 0 < (f 0)^(-alpha)+lambda*alpha*t :=
    add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos hz0 _)
      (mul_nonneg (mul_nonneg hl ha.le) ht.1)
  have hinverse := Real.rpow_le_rpow_of_nonpos hbase hbound
    (show -(1/alpha) ≤ 0 from neg_nonpos.mpr (div_nonneg zero_le_one ha.le))
  have hleft : ((f t)^(-alpha))^(-(1/alpha)) = f t := by
    rw [← Real.rpow_mul htpos.le]
    have he : (-alpha)*(-(1/alpha)) = 1 := by field_simp [ne_of_gt ha]
    rw [he,Real.rpow_one]
  rw [hleft, ← powerDecayProfile_eq_inverse_power hl ha hz0 ht.1] at hinverse
  exact hinverse

/-- The original printed denominator when alpha=(p-2)/2. -/
theorem powerDecayProfile_source_form (lambda p z0 t : Real) :
    powerDecayProfile lambda ((p-2)/2) z0 t =
      z0 / (1 + (lambda*(p-2)/2)*z0^((p-2)/2)*t)^(2/(p-2)) := by
  have he : (1 : Real)/((p-2)/2) = 2/(p-2) := by
    by_cases hp : p-2 = 0
    · simp [hp]
    · field_simp [hp]
  have hb : 1+lambda*((p-2)/2)*z0^((p-2)/2)*t =
      1+(lambda*(p-2)/2)*z0^((p-2)/2)*t := by ring
  simp only [powerDecayProfile,he,hb]

end PaperFormalization.MatrixFactorization
