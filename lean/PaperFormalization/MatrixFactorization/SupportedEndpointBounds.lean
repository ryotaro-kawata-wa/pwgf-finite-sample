import PaperFormalization.MatrixFactorization.PrimalTimeLabelBounds

/-! # MF24: lift continuous endpoint bounds, not arbitrary field representatives

Verification status and conditional scope: see `MF24_VALIDATION.md`. A fixed-time endpoint displacement is continuous on the
original support. Its AE bound therefore extends to every support point, even
for atomic/singular measures. Applying this argument separately to EACH time
pair gives all-pair supported control without an uncountable AE intersection.
Velocity representatives themselves are not presumed continuous or identified
on null support subsets. The source must still supply an integrated trajectory
estimate before the endpoint lemmas can be applied to its WGF.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Relative continuity on the closed support suffices to lift a scalar bound. -/
theorem support_le_of_continuousOn_ae {d : Nat} (mu : Measure (UnitSphere d))
    (f : UnitSphere d → Real) (hf : ContinuousOn f mu.support) (C : Real)
    (hb : ∀ᵐ w ∂mu, f w ≤ C) : ∀ w ∈ mu.support, f w ≤ C := by
  intro w hw
  by_contra hn
  have hl : C < f w := lt_of_not_ge hn
  have hpre : f ⁻¹' Ioi C ∈ 𝓝[mu.support] w :=
    (hf w hw).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hl)
  obtain ⟨U, hU, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  have hpos := (Measure.mem_support_iff_forall w).mp hw U hU
  have hnot : ∀ᵐ y ∂mu, y ∉ U := by
    filter_upwards [hb, Measure.support_mem_ae (μ := mu)] with y hy hs
    intro hyU
    have hgt : C < f y := hsub ⟨hyU, hs⟩
    exact (not_lt_of_ge hy) hgt
  have hzero : mu U = 0 := by simpa using (ae_iff.mp hnot)
  exact (ne_of_gt hpos) hzero

theorem support_dist_le_of_ae {d : Nat} {E : Type*} [PseudoMetricSpace E]
    (mu : Measure (UnitSphere d)) (f k : UnitSphere d → E)
    (hf : ContinuousOn f mu.support) (hk : ContinuousOn k mu.support) (C : Real)
    (hb : ∀ᵐ w ∂mu, dist (f w) (k w) ≤ C) :
    ∀ w ∈ mu.support, dist (f w) (k w) ≤ C :=
  support_le_of_continuousOn_ae mu (fun w => dist (f w) (k w))
    (fun w hw => (hf w hw).dist (hk w hw)) C hb

/-- Endpoint maps that agree almost everywhere agree at every supported label. -/
theorem support_eq_of_ae {d : Nat} {E : Type*} [MetricSpace E]
    (mu : Measure (UnitSphere d)) (f k : UnitSphere d → E)
    (hf : ContinuousOn f mu.support) (hk : ContinuousOn k mu.support) (he : f =ᵐ[mu] k) :
    ∀ w ∈ mu.support, f w = k w := by
  have hb := support_dist_le_of_ae mu f k hf hk 0 (by
    filter_upwards [he] with w hw
    simp only [hw, dist_self, le_refl])
  intro w hw
  exact dist_eq_zero.mp (le_antisymm (hb w hw) dist_nonneg)

/-- The AE set is allowed to depend on (s,t). It is lifted before quantifying
over all times, so no interchange of an uncountable AE intersection occurs. -/
theorem supported_endpoints_lipschitz {d : Nat} {E : Type*} [PseudoMetricSpace E]
    (mu : Measure (UnitSphere d)) (Phi : Real → UnitSphere d → E)
    (D : Set Real) (K : Real) (hK : 0 ≤ K)
    (hc : ∀ t ∈ D, ContinuousOn (Phi t) mu.support)
    (hb : ∀ s ∈ D, ∀ t ∈ D, ∀ᵐ w ∂mu,
      dist (Phi s w) (Phi t w) ≤ K*dist s t) :
    ∀ w ∈ mu.support, LipschitzOnWith (Real.nnabs K) (fun t => Phi t w) D := by
  intro w hw
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have h := support_dist_le_of_ae mu (Phi s) (Phi t) (hc s hs) (hc t ht) (K*dist s t) (hb s hs t ht) w hw
  simpa only [Real.coe_nnabs, abs_of_nonneg hK] using h

/-- Uniform time bounds and separate spatial continuity imply the required
supported joint continuity. No cap assumption is used in this general lemma. -/
theorem supported_joint_continuity_of_ae_endpoint_bound {d : Nat} {E : Type*} [PseudoMetricSpace E]
    (mu : Measure (UnitSphere d)) (Phi : Real → UnitSphere d → E)
    (D : Set Real) (K : Real) (hK : 0 ≤ K)
    (hc : ∀ t ∈ D, ContinuousOn (Phi t) mu.support)
    (hb : ∀ s ∈ D, ∀ t ∈ D, ∀ᵐ w ∂mu,
      dist (Phi s w) (Phi t w) ≤ K*dist s t) :
    ContinuousOn (fun tw : Real × UnitSphere d => Phi tw.1 tw.2) (D ×ˢ mu.support) := by
  have hL := supported_endpoints_lipschitz mu Phi D K hK hc hb
  rintro ⟨t,w⟩ ⟨ht,hw⟩
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨delta, hdelta, hspace⟩ := Metric.continuousWithinAt_iff.mp
    (hc t ht w hw) (eps/2) (by positivity)
  refine ⟨min delta (eps/(2*(K+1))), lt_min hdelta (by positivity), ?_⟩
  rintro ⟨s,u⟩ ⟨hs,hu⟩ hsu
  rw [Prod.dist_eq] at hsu
  have hst : dist s t < eps/(2*(K+1)) :=
    (le_max_left _ _).trans_lt (hsu.trans_le (min_le_right _ _))
  have huw : dist u w < delta := (le_max_right _ _).trans_lt (hsu.trans_le (min_le_left _ _))
  have hsp := hspace hu huw
  have htime := (hL u hu).dist_le_mul s hs t ht
  have htime' : dist (Phi s u) (Phi t u) ≤ K*dist s t := by
    simpa only [Real.coe_nnabs, abs_of_nonneg hK] using htime
  have htimelt : dist (Phi s u) (Phi t u) < eps/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*(K+1) by positivity)).mp hst
    nlinarith [dist_nonneg (x := s) (y := t)]
  exact (dist_triangle (Phi s u) (Phi t u) (Phi t w)).trans_lt (by linarith)

end PaperFormalization.MatrixFactorization
