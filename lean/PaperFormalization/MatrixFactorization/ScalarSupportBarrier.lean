import PaperFormalization.MatrixFactorization.ScalarCapBarrier

/-! # A pointwise upper barrier with derivatives only above its level

This scalar adapter is intended for the half squared distance of an individual
characteristic. It requires no derivative at the closed time endpoints and no derivative sign
condition at the barrier level itself. The model must supply its actual curve inequality.
-/
open Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A differentiable curve cannot rise above a level when its derivative is
nonpositive everywhere strictly above that level. -/
theorem scalar_support_barrier {f : Real → Real} {T R : Real}
    (hc : ContinuousOn f (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt Real f t)
    (hinit : f 0 ≤ R)
    (hn : ∀ t ∈ Ioo 0 T, R < f t → deriv f t ≤ 0) :
    ∀ t ∈ Icc 0 T, f t ≤ R := by
  intro t ht
  by_contra hbad
  have hbad : R < f t := lt_of_not_ge hbad
  let K : Set Real := Icc 0 t ∩ f ⁻¹' Iic R
  have hct : ContinuousOn f (Icc 0 t) := hc.mono (Icc_subset_Icc le_rfl ht.2)
  have hKclosed : IsClosed K := hct.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hKcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
  have hKnonempty : K.Nonempty := ⟨0,⟨le_rfl,ht.1⟩,hinit⟩
  obtain ⟨u,hu,hmax⟩ := hKcompact.exists_isMaxOn hKnonempty continuous_id.continuousOn
  have hut : u ∈ Icc 0 t := hu.1
  have huR : f u ≤ R := hu.2
  have hafter : ∀ s ∈ Ioo u t, R < f s := by
    intro s hs
    by_contra hsr
    have hsK : s ∈ K := ⟨⟨hut.1.trans hs.1.le,hs.2.le⟩,le_of_not_gt hsr⟩
    exact (not_le_of_gt hs.1) (hmax hsK)
  have hanti : AntitoneOn f (Icc u t) := scalar_antitone_on_closed_interval
    (hc.mono (Icc_subset_Icc hut.1 ht.2))
    (fun s hs => hd s ⟨hut.1.trans_lt hs.1,hs.2.trans_le ht.2⟩)
    (fun s hs => hn s ⟨hut.1.trans_lt hs.1,hs.2.trans_le ht.2⟩ (hafter s hs))
  have hft : f t ≤ f u := hanti ⟨le_rfl,hut.2⟩ ⟨hut.2,le_rfl⟩ hut.2
  exact (not_le_of_gt hbad) (hft.trans huR)

end PaperFormalization.MatrixFactorization
