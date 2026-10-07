import Mathlib

/-! # MF15: a scalar first-exit barrier on a closed cap interval

This elementary lemma is an analytic
adapter, not an assumption about the particle model. The model application
must supply continuity and the local derivative inequality. Derivatives are
required only in the open time interval, so T=0 and both time endpoints are
retained. A STRICT outer threshold is essential: the later application uses
a larger auxiliary threshold, not a stricter hypothesis on the initial state.
-/
open Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- Convenience wrapper exposing precisely the interior-time derivative input. -/
theorem scalar_antitone_on_closed_interval {f : Real → Real} {a b : Real}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt Real f t)
    (hn : ∀ t ∈ Ioo a b, deriv f t ≤ 0) : AntitoneOn f (Icc a b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
  · rw [interior_Icc]
    exact fun t ht => (hd t ht).differentiableWithinAt
  · simpa only [interior_Icc] using hn

/-- Local nonincrease below a threshold prevents a first exit, and hence gives
nonincrease on the entire given interval. No current-time smallness premise
survives in the conclusion. This does NOT establish that a cap interval exists. -/
theorem scalar_cap_barrier {f : Real → Real} {T R : Real}
    (hT : 0 ≤ T) (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hinit : f 0 < R)
    (hn : ∀ t ∈ Ioo 0 T, f t < R → deriv f t ≤ 0) :
    (∀ t ∈ Icc 0 T, f t < R) ∧ AntitoneOn f (Icc 0 T) := by
  have hstay : ∀ t ∈ Icc 0 T, f t < R := by
    intro t ht
    by_contra hbad
    have hbad : R ≤ f t := le_of_not_gt hbad
    let K : Set Real := Icc 0 T ∩ f ⁻¹' Ici R
    have hKclosed : IsClosed K :=
      hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hKcompact : IsCompact K :=
      isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
    have hKnonempty : K.Nonempty := ⟨t, ht, hbad⟩
    obtain ⟨u, hu, hmin⟩ := hKcompact.exists_isMinOn hKnonempty continuous_id.continuousOn
    have huT : u ∈ Icc 0 T := hu.1
    have huR : R ≤ f u := hu.2
    have hbefore : ∀ s ∈ Ioo 0 u, f s < R := by
      intro s hs
      by_contra hsR
      have hsK : s ∈ K := ⟨⟨hs.1.le, hs.2.le.trans huT.2⟩, le_of_not_gt hsR⟩
      have hus : u ≤ s := hmin hsK
      exact (not_le_of_gt hs.2) hus
    have hanti : AntitoneOn f (Icc 0 u) :=
      scalar_antitone_on_closed_interval
        (hc.mono (Icc_subset_Icc le_rfl huT.2))
        (fun s hs => hd s ⟨hs.1, hs.2.trans_le huT.2⟩)
        (fun s hs => hn s ⟨hs.1, hs.2.trans_le huT.2⟩ (hbefore s hs))
    have hle : f u ≤ f 0 := hanti ⟨le_rfl, huT.1⟩ ⟨huT.1, le_rfl⟩ huT.1
    exact (not_le_of_gt hinit) (huR.trans hle)
  refine ⟨hstay, scalar_antitone_on_closed_interval hc hd ?_⟩
  exact fun t ht => hn t ht (hstay t ⟨ht.1.le, ht.2.le⟩)

/-- Once a nonnegative nonincreasing quantity reaches zero, it stays zero.
No inverse power is evaluated at zero, and no uniqueness theorem is needed. -/
theorem scalar_zero_persists {f : Real → Real} {T s t : Real}
    (hnonneg : ∀ u ∈ Icc 0 T, 0 ≤ f u) (hanti : AntitoneOn f (Icc 0 T))
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) (hz : f s = 0) :
    f t = 0 := by
  apply le_antisymm
  · simpa only [hz] using hanti hs ht hst
  · exact hnonneg t ht

end PaperFormalization.MatrixFactorization
