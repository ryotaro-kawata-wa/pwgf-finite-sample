import Mathlib

/-! # Scalar continuation from a uniform improvement on good prefixes

This topological adapter does not assume that all times are cap-admissible.
Continuity and an improvement valid on each admissible closed prefix exclude
a first intermediate-level hit. Applications must separately derive this
continuity and the prefix improvement from their actual global curve.
-/
open Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A fixed strict improvement on every cap-admissible closed prefix prevents
any cap exit, including when the only initially supplied prefix has length zero. -/
theorem scalar_cap_continuation {R : Real → Real} {cap B : Real}
    (hc : ContinuousOn R (Ici 0)) (hinit : R 0 < cap) (hB : B < cap)
    (hprefix : ∀ T : Real, 0 ≤ T → (∀ t ∈ Icc (0 : Real) T, R t < cap) →
      ∀ t ∈ Icc (0 : Real) T, R t ≤ B) :
    (∀ t : Real, 0 ≤ t → R t < cap) ∧ (∀ t : Real, 0 ≤ t → R t ≤ B) := by
  have hzero : R 0 ≤ B := by
    apply hprefix 0 le_rfl ?_ 0 ⟨le_rfl,le_rfl⟩
    intro t ht
    have he : t = 0 := le_antisymm ht.2 ht.1
    simpa only [he] using hinit
  let M := (B+cap)/2
  have hBM : B < M := by dsimp only [M]; linarith
  have hMc : M < cap := by dsimp only [M]; linarith
  have hRM : R 0 < M := hzero.trans_lt hBM
  have hstay : ∀ t : Real, 0 ≤ t → R t < cap := by
    intro t ht
    by_contra hbad
    have hMt : M ≤ R t := hMc.le.trans (le_of_not_gt hbad)
    have hct : ContinuousOn R (Icc 0 t) := hc.mono Icc_subset_Ici_self
    obtain ⟨u0,hu0,hu0M⟩ := intermediate_value_Icc ht hct ⟨hRM.le,hMt⟩
    let K : Set Real := Icc 0 t ∩ R ⁻¹' {M}
    have hKclosed : IsClosed K :=
      hct.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hKcompact : IsCompact K :=
      isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
    have hKnonempty : K.Nonempty := ⟨u0,hu0,hu0M⟩
    obtain ⟨u,hu,hmin⟩ := hKcompact.exists_isMinOn hKnonempty continuous_id.continuousOn
    have hut : u ∈ Icc 0 t := hu.1
    have huM : R u = M := hu.2
    have hgood : ∀ s ∈ Icc (0 : Real) u, R s < cap := by
      intro s hs
      by_cases hsM : R s < M
      · exact hsM.trans hMc
      have hcs : ContinuousOn R (Icc 0 s) := hc.mono Icc_subset_Ici_self
      obtain ⟨v,hv,hvM⟩ := intermediate_value_Icc hs.1 hcs ⟨hRM.le,le_of_not_gt hsM⟩
      have hvK : v ∈ K := ⟨⟨hv.1,hv.2.trans (hs.2.trans hut.2)⟩,hvM⟩
      have hus : u ≤ s := (hmin hvK).trans hv.2
      have hsu : s = u := le_antisymm hs.2 hus
      simpa only [hsu,huM] using hMc
    have hub := hprefix u hut.1 hgood u ⟨hut.1,le_rfl⟩
    rw [huM] at hub
    exact (not_le_of_gt hBM) hub
  exact ⟨hstay,fun t ht => hprefix t ht (fun s hs => hstay s hs.1) t ⟨ht,le_rfl⟩⟩

end PaperFormalization.MatrixFactorization
