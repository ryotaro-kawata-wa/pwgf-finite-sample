import PaperFormalization.Manuscript.SourceMainRateStatement

/-! # A uniform power-law consequence of the original pointwise rate

M13t verified implementation. These deterministic consequences use the same
response and confidence hypotheses as the main theorem. There is no new
probability event. Choosing the upstream exponent epsilon/(5/4+Cp) yields
N^(-1/4+upsilon+epsilon). Real suprema are used only after an explicit bound.
This is not an instantiation of a particular example's stochastic dynamics.
-/
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace PaperFormalization.Manuscript
open Continuous

/-- The main-text scale has a polynomial bound with no jump/speed factor. -/
theorem sourceMainXi_polynomial_le (N : Nat) (T p upsilon zeta Cp : Real)
    (hN : 0 < N) (hp : 0 < p) (hu : 0 ≤ upsilon) (hz : 0 ≤ zeta)
    (hT : T ≤ (N : Real)^(1/4-upsilon-zeta)) (hpN : (N : Real)^(-Cp) ≤ p) :
    sourceMainXi N T p ≤ (Real.exp 1+1)*(N : Real)^(5/4+Cp) := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : Real) := by exact_mod_cast hN
  have hnq : 1 ≤ (N : Real)^(1/4 : Real) := Real.one_le_rpow hn (by norm_num)
  have hTq := hT.trans (Real.rpow_le_rpow_of_exponent_le hn (show (1/4-upsilon-zeta : Real) ≤ 1/4 by linarith))
  have htime : Real.exp 1+T ≤ (Real.exp 1+1)*(N : Real)^(1/4 : Real) := by
    nlinarith [mul_le_mul_of_nonneg_left hnq (Real.exp_pos 1).le]
  have hinv : p⁻¹ ≤ (N : Real)^Cp := by
    have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hn0 (-Cp)) hpN
    simpa only [one_div,Real.rpow_neg hn0.le,inv_inv] using hi
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul htime hinv (by positivity) (by positivity)) hn0.le
  calc
    sourceMainXi N T p = (N : Real)*((Real.exp 1+T)*p⁻¹) := by unfold sourceMainXi; ring
    _ ≤ (N : Real)*(((Real.exp 1+1)*(N : Real)^(1/4 : Real))*(N : Real)^Cp) := hm
    _ = (Real.exp 1+1)*((N : Real)^(1 : Real)*(N : Real)^(1/4 : Real)*(N : Real)^Cp) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hn0,← Real.rpow_add hn0]; congr 2; ring

/-- Prefix responses are no larger than the whole scheduled response. -/
theorem sourceRateJumpResponse_prefix_le
    (kappa : Real -> Real) (tau eta : Nat -> Real) (K J : Nat) (t : Real)
    (hK : K ≤ J) (heta : ∀ i < J, 0 ≤ eta i) :
    sourceRateJumpResponse kappa tau eta K t ≤ sourceRateJumpResponse kappa tau eta J t := by
  unfold sourceRateJumpResponse
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hi).1) hK),(Finset.mem_filter.mp hi).2⟩
  · intro i hi _
    exact mul_nonneg (heta i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)) (propagator_nonneg _ _ _)

set_option maxHeartbeats 1000000 in
/-- A uniform-in-time profile bound; no supremum or hidden boundedness premise. -/
theorem sourceAsymptoticProfile_power_le
    (N J K : Nat) (T t upsilon zeta C0 : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (hN : 0 < N) (hK : K ≤ J) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    (hu : 0 ≤ upsilon) (hz : 0 ≤ zeta) (hC0 : 0 ≤ C0)
    (hTN : T ≤ (N : Real)^(1/4-upsilon-zeta))
    (heta : ∀ i < J, 0 ≤ eta i)
    (hResponse : SourceControlledResponse N J T upsilon C0 kappa tau eta) :
    sourceAsymptoticProfile N K T kappa tau eta t ≤ (2+6*C0)*(N : Real)^(-1/4+upsilon) := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : Real) := by exact_mod_cast hN
  have hTNq : T ≤ (N : Real)^(1/4 : Real) := hTN.trans
    (Real.rpow_le_rpow_of_exponent_le hn (by linarith))
  have hTNs := source_growing_horizon_le_sqrt N T upsilon zeta hN hu hz hTN
  obtain ⟨ha,hb⟩ := source_short_horizon_residual_rates N T hN hTNs
  have hc0 := sourceRateContinuousResponse_nonneg kappa t ht.1
  have hj0 := sourceRateJumpResponse_nonneg kappa tau eta K t (fun i hi => heta i (lt_of_lt_of_le hi hK))
  have hc := hResponse.1 t ht
  have hj := (sourceRateJumpResponse_prefix_le kappa tau eta K J t hK heta).trans (hResponse.2 t ht)
  have hbound : sourceAsymptoticProfile N K T kappa tau eta t ≤
      2*(Real.sqrt N)⁻¹*(1+C0*(N : Real)^upsilon*(1+T))+
      2*(N : Real)^(-1/4 : Real)*(C0*(N : Real)^upsilon) := by
    unfold sourceAsymptoticProfile
    exact add_le_add (mul_le_mul ha (add_le_add le_rfl hc) (by positivity) (by positivity))
      (mul_le_mul hb hj hj0 (by positivity))
  have htime : 1+T ≤ 2*(N : Real)^(1/4 : Real) := by
    linarith [Real.one_le_rpow hn (show (0 : Real) ≤ 1/4 by norm_num)]
  have hcTime := mul_le_mul_of_nonneg_left htime (show 0 ≤ C0*(N : Real)^upsilon by positivity)
  have hcont := mul_le_mul_of_nonneg_left (add_le_add (show (1 : Real) ≤ 1 from le_rfl) hcTime)
    (show 0 ≤ 2*(Real.sqrt N)⁻¹ by positivity)
  have hinv : (Real.sqrt N)⁻¹ = (N : Real)^(-1/2 : Real) := by
    rw [Real.sqrt_eq_rpow,show (-1/2 : Real)=-(1/2 : Real) by ring,Real.rpow_neg hn0.le]
  have hprod : (N : Real)^(-1/2 : Real)*(N : Real)^upsilon*(N : Real)^(1/4 : Real) =
      (N : Real)^(-1/4+upsilon) := by
    rw [← Real.rpow_add hn0,← Real.rpow_add hn0]; congr 1; ring
  have hjprod : (N : Real)^(-1/4 : Real)*(N : Real)^upsilon = (N : Real)^(-1/4+upsilon) :=
    (Real.rpow_add hn0 _ _).symm
  have hhalf := Real.rpow_le_rpow_of_exponent_le hn (show (-1/2 : Real) ≤ -1/4+upsilon by linarith)
  have heq : 2*(Real.sqrt N)⁻¹*(1+C0*(N : Real)^upsilon*(2*(N : Real)^(1/4 : Real)))+
      2*(N : Real)^(-1/4 : Real)*(C0*(N : Real)^upsilon) =
      2*(N : Real)^(-1/2 : Real)+6*C0*(N : Real)^(-1/4+upsilon) := by
    rw [hinv]
    calc
      _ = 2*(N : Real)^(-1/2 : Real)+
          4*C0*((N : Real)^(-1/2 : Real)*(N : Real)^upsilon*(N : Real)^(1/4 : Real))+
          2*C0*((N : Real)^(-1/4 : Real)*(N : Real)^upsilon) := by ring
      _ = _ := by rw [hprod,hjprod]; ring
  have hh := hbound.trans (add_le_add hcont le_rfl)
  rw [heq] at hh
  nlinarith

/-- Expose the polynomial consequence of a MAIN-Xi bound. Choosing
s=epsilon/(5/4+Cp) in the epsilon-free event gives the desired epsilon loss. -/
theorem source_pointwise_main_rate_to_power
    (N J K : Nat) (T t confidence upsilon zeta C0 Cp M s loss r : Real)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (hN : 0 < N) (hK : K ≤ J) (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    (hu : 0 ≤ upsilon) (hz : 0 ≤ zeta) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hTN : T ≤ (N : Real)^(1/4-upsilon-zeta)) (hp : 0 < confidence)
    (hpN : (N : Real)^(-Cp) ≤ confidence) (hLoss : (5/4+Cp)*s ≤ loss)
    (heta : ∀ i < J, 0 ≤ eta i)
    (hResponse : SourceControlledResponse N J T upsilon C0 kappa tau eta)
    (hr : r ≤ M*(sourceMainXi N T confidence)^s*sourceAsymptoticProfile N K T kappa tau eta t) :
    r ≤ (M*(Real.exp 1+1)^s*(2+6*C0))*(N : Real)^(-1/4+upsilon+loss) := by
  have hn : (1 : Real) ≤ N := by exact_mod_cast hN
  have hn0 : 0 < (N : Real) := by exact_mod_cast hN
  have hx := sourceMainXi_polynomial_le N T confidence upsilon zeta Cp hN hp hu hz hTN hpN
  have hpow := Real.rpow_le_rpow (show 0 ≤ sourceMainXi N T confidence by unfold sourceMainXi; positivity) hx hs
  rw [Real.mul_rpow (by positivity : 0 ≤ Real.exp 1+1) (by positivity : 0 ≤ (N : Real)^(5/4+Cp)),
    ← Real.rpow_mul hn0.le] at hpow
  have hpow' := hpow.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn hLoss) (by positivity))
  have hprofile := sourceAsymptoticProfile_power_le N J K T t upsilon zeta C0 kappa tau eta
    hN hK hT ht hu hz hC0 hTN heta hResponse
  have hnonneg := sourceAsymptoticProfile_nonneg N K T t kappa tau eta hT ht.1 (fun i hi => heta i (lt_of_lt_of_le hi hK))
  calc
    r ≤ M*(sourceMainXi N T confidence)^s*sourceAsymptoticProfile N K T kappa tau eta t := hr
    _ ≤ (M*((Real.exp 1+1)^s*(N : Real)^loss))*((2+6*C0)*(N : Real)^(-1/4+upsilon)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow' hM) hprofile hnonneg (by positivity)
    _ = (M*(Real.exp 1+1)^s*(2+6*C0))*((N : Real)^loss*(N : Real)^(-1/4+upsilon)) := by ring
    _ = _ := by rw [← Real.rpow_add hn0]; congr 2; ring

/-- Bound the real supremum only after providing its boundedness and a
nonempty interval; T=0 is included. -/
theorem source_uniform_error_sup_bound (error : Real -> Real) (T bound : Real)
    (hT : 0 ≤ T) (hbound : ∀ t ∈ Icc 0 T, error t ≤ bound) :
    BddAbove (error '' Icc 0 T) ∧ sSup (error '' Icc 0 T) ≤ bound := by
  have hb : BddAbove (error '' Icc 0 T) := ⟨bound,by rintro _ ⟨t,ht,rfl⟩; exact hbound t ht⟩
  refine ⟨hb,csSup_le ⟨error 0,0,⟨le_rfl,hT⟩,rfl⟩ ?_⟩
  rintro _ ⟨t,ht,rfl⟩
  exact hbound t ht

/-- The uniform majorant actually tends to zero when its exponent is negative.
No convergence of a conditioned probability measure is asserted. -/
theorem source_rate_power_tendsto_zero (M upsilon loss : Real) (h : upsilon+loss < 1/4) :
    Tendsto (fun N : Nat => M*(N : Real)^(-1/4+upsilon+loss)) atTop (nhds 0) := by
  have hpos : 0 < 1/4-upsilon-loss := by linarith
  have ht := ((tendsto_rpow_neg_atTop hpos).comp tendsto_natCast_atTop_atTop).const_mul M
  simpa only [show -(1/4-upsilon-loss)=(-1/4+upsilon+loss : Real) by ring,mul_zero,Function.comp_def] using ht

/-- Apply the scalar power estimate directly to the actual joint conclusion.
The right-path supremum is bounded before it is compared; the true pretraces
retain their own population laws and genuine integrability certificates. -/
theorem source_joint_rate_uniform_power
    {N d : Nat} {H : Nat -> Type*}
    [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace Real (H n)]
    [∀ n, CompleteSpace (H n)]
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (law : Real -> Measure (EuclideanSpace Real (Fin d)))
    (preLaw : Nat -> Measure (EuclideanSpace Real (Fin d)))
    (X Y : Real -> SourceFiniteConfiguration N d)
    (preX preY : Nat -> SourceFiniteConfiguration N d)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T confidence upsilon zeta C0 Cp M s loss : Real)
    (hN : 0 < N) (hT : 0 ≤ T)
    (htau0 : tau 0 = 0) (htime : ∀ k < J, tau k < tau (k+1)) (hLast : tau J ≤ T)
    (hu : 0 ≤ upsilon) (hz : 0 ≤ zeta) (hC0 : 0 ≤ C0) (hM : 0 ≤ M) (hs : 0 ≤ s)
    (hTN : T ≤ (N : Real)^(1/4-upsilon-zeta)) (hp : 0 < confidence)
    (hpN : (N : Real)^(-Cp) ≤ confidence) (hLoss : (5/4+Cp)*s ≤ loss)
    (heta : ∀ i < J, 0 ≤ eta i)
    (hResponse : SourceControlledResponse N J T upsilon C0 kappa tau eta)
    (hJoint : SourceJointRateConclusion F G law preLaw X Y preX preY
      kappa tau eta J T confidence s M) :
    let error := fun t => max (norm (X t-Y t)/Real.sqrt N) (sourceObjectiveError F G (law t) (X t))
    let bound := (M*(Real.exp 1+1)^s*(2+6*C0))*(N : Real)^(-1/4+upsilon+loss)
    (∀ t ∈ Icc 0 T, Integrable F (law t) ∧ error t ≤ bound) ∧
    (∀ k < J, Integrable F (preLaw k) ∧
      max (norm (preX k-preY k)/Real.sqrt N) (sourceObjectiveError F G (preLaw k) (preX k)) ≤ bound) ∧
    BddAbove (error '' Icc 0 T) ∧ sSup (error '' Icc 0 T) ≤ bound := by
  dsimp only
  have hRight : ∀ t ∈ Icc 0 T,
      max (norm (X t-Y t)/Real.sqrt N) (sourceObjectiveError F G (law t) (X t)) ≤
        (M*(Real.exp 1+1)^s*(2+6*C0))*(N : Real)^(-1/4+upsilon+loss) := by
    intro t ht
    exact source_pointwise_main_rate_to_power N J J T t confidence upsilon zeta C0 Cp M s loss _
      kappa tau eta hN le_rfl hT ht hu hz hC0 hM hs hTN hp hpN hLoss heta hResponse (hJoint.1 t ht).2
  refine ⟨fun t ht => ⟨(hJoint.1 t ht).1,hRight t ht⟩,?_,?_⟩
  · intro k hk
    have ht : tau (k+1) ∈ Icc 0 T := source_closed_time_in_horizon tau J T
      htau0 htime hLast k hk.le (tau (k+1))
      (by simp only [if_pos hk]; exact ⟨(htime k hk).le,le_rfl⟩)
    exact ⟨(hJoint.2 k hk).1,
      source_pointwise_main_rate_to_power N J k T (tau (k+1)) confidence upsilon zeta C0 Cp M s loss _
        kappa tau eta hN hk.le hT ht hu hz hC0 hM hs hTN hp hpN hLoss heta hResponse (hJoint.2 k hk).2⟩
  · exact source_uniform_error_sup_bound _ T _ hT hRight

end PaperFormalization.Manuscript
