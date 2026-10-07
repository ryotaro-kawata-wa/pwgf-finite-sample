import PaperFormalization.Manuscript.AdaptiveRadiusGrid
import PaperFormalization.Manuscript.SourceMomentTail

/-! # Uniform radius for the two actual clouds under their original law

Only unconditional one-particle moment bounds and one common AE branchwise
Lipschitz event are used. The actual adaptive grid has both endpoint labels,
including zero-length branches. No particle, time, or cloud independence is
assumed. Each branch is a supplied closed representative: identifying its
one-sided traces with the model is a separate deterministic application.
-/
open Set MeasureTheory
open scoped BigOperators NNReal
namespace PaperFormalization.Manuscript

variable {E Ω : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

set_option maxHeartbeats 800000 in
/-- Actual all-real-order source moments give the manuscript's exact
2N[2(J+1)+2BT/D] exponential uniform-radius bound. The continuum failure set
need not be assumed measurable: the conclusion is an outer-measure bound. -/
theorem source_two_cloud_uniform_radius_tail_le
    (J N : ℕ) (alpha K D T : ℝ) (B : ℝ≥0) (a b : Fin (J+1) → ℝ)
    (halpha : 0 < alpha) (hK : 0 < K) (hD : 2 * Real.exp 1 * K ≤ D)
    (hab : ∀ j, a j ≤ b j) (hT : ∑ j, (b j-a j) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Z : Fin 2 → Fin N → Fin (J+1) → Ω → ℝ → E)
    (hLip : ∀ᵐ ω ∂ν, ∀ c i j, LipschitzOnWith B (Z c i j ω) (Icc (a j) (b j)))
    (hMarginal : ∀ c i j t, t ∈ Icc (a j) (b j) →
      ν.map (fun ω => Z c i j ω t) ∈ sourceMomentClass alpha K) :
    ν.real {ω | ∃ c i j t, t ∈ Icc (a j) (b j) ∧ D < ‖Z c i j ω t‖} ≤
      2 * N * (2 * ((J : ℝ)+1) + 2 * (B : ℝ) * T / D) *
        Real.exp (-((D / (2 * Real.exp 1 * K)) ^ alpha)) := by
  let M : Fin (J+1) → ℕ := fun j => radiusBranchSubdivisions B D (a j) (b j)
  let tail := Real.exp (-((D / (2 * Real.exp 1 * K)) ^ alpha))
  let NodeBad (c : Fin 2) (i : Fin N) (j : Fin (J+1)) (k : Fin (M j+1)) : Set Ω :=
    {ω | D/2 < ‖Z c i j ω (closedBranchGrid (a j) (b j) (M j) k)‖}
  let Nodes : Set Ω := ⋃ c, ⋃ i, ⋃ j, ⋃ k, NodeBad c i j k
  let NotLip : Set Ω := {ω | ¬ ∀ c i j, LipschitzOnWith B (Z c i j ω) (Icc (a j) (b j))}
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hnode (c : Fin 2) (i : Fin N) (j : Fin (J+1)) (k : Fin (M j+1)) :
      ν.real (NodeBad c i j k) ≤ tail := by
    let t := closedBranchGrid (a j) (b j) (M j) k
    have ht : t ∈ Icc (a j) (b j) := closedBranchGrid_mem (a j) (b j) (hab j)
      (radiusBranchSubdivisions_pos B D (a j) (b j)) k
    have hm := hMarginal c i j t ht
    letI : IsProbabilityMeasure (ν.map (fun ω => Z c i j ω t)) := hm.1
    have hZ : AEMeasurable (fun ω => Z c i j ω t) ν :=
      aemeasurable_of_map_neZero (by infer_instance)
    have he := map_measureReal_apply_of_aemeasurable hZ
      (measurableSet_lt measurable_const measurable_norm : MeasurableSet {x : E | D/2 < ‖x‖})
    have hb := sourceMomentClass_norm_tail_exp_le alpha K (D/2) halpha hK
      (by linarith) (ν.map (fun ω => Z c i j ω t)) hm
    have hratio : (D/2) / (Real.exp 1 * K) = D / (2 * Real.exp 1 * K) := by ring
    rw [hratio] at hb
    exact he ▸ hb
  have hbranch (c : Fin 2) (i : Fin N) (j : Fin (J+1)) :
      ν.real (⋃ k, NodeBad c i j k) ≤ ((M j : ℝ)+1)*tail := by
    calc
      _ ≤ ∑ k, ν.real (NodeBad c i j k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _k : Fin (M j+1), tail := Finset.sum_le_sum (fun k _ => hnode c i j k)
      _ = _ := by simp
  have hparticle (c : Fin 2) (i : Fin N) :
      ν.real (⋃ j, ⋃ k, NodeBad c i j k) ≤ (∑ j, ((M j : ℝ)+1))*tail := by
    calc
      _ ≤ ∑ j, ν.real (⋃ k, NodeBad c i j k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ j, ((M j : ℝ)+1)*tail := Finset.sum_le_sum (fun j _ => hbranch c i j)
      _ = _ := by rw [Finset.sum_mul]
  have hcloud (c : Fin 2) :
      ν.real (⋃ i, ⋃ j, ⋃ k, NodeBad c i j k) ≤ N * ((∑ j, ((M j : ℝ)+1))*tail) := by
    calc
      _ ≤ ∑ i, ν.real (⋃ j, ⋃ k, NodeBad c i j k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : Fin N, (∑ j, ((M j : ℝ)+1))*tail :=
        Finset.sum_le_sum (fun i _ => hparticle c i)
      _ = _ := by simp
  have hnodes : ν.real Nodes ≤ 2 * N * (∑ j, ((M j : ℝ)+1))*tail := by
    calc
      _ ≤ ∑ c, ν.real (⋃ i, ⋃ j, ⋃ k, NodeBad c i j k) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _c : Fin 2, N * ((∑ j, ((M j : ℝ)+1))*tail) :=
        Finset.sum_le_sum (fun c _ => hcloud c)
      _ = _ := by simp; ring
  have hcard : (∑ j, ((M j : ℝ)+1)) ≤
      2 * ((J : ℝ)+1) + 2 * (B : ℝ) * T / D := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      radiusBranchGrid_total_card_le B D T a b hD0 hab hT
  have hnull : ν.real NotLip = 0 := (measureReal_eq_zero_iff).mpr (ae_iff.mp hLip)
  have hsub : {ω | ∃ c i j t, t ∈ Icc (a j) (b j) ∧ D < ‖Z c i j ω t‖} ⊆
      NotLip ∪ Nodes := by
    intro ω hω
    by_cases hpath : ω ∈ NotLip
    · exact Or.inl hpath
    right
    have hp : ∀ c i j, LipschitzOnWith B (Z c i j ω) (Icc (a j) (b j)) :=
      not_not.mp hpath
    obtain ⟨c,i,j,t,ht,hbad⟩ := hω
    by_contra hn
    have hg : ∀ k, ‖Z c i j ω (closedBranchGrid (a j) (b j) (M j) k)‖ ≤ D/2 := by
      intro k
      exact le_of_not_gt (fun hk => hn (mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨i,
        mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨k,hk⟩⟩⟩⟩))
    exact (not_lt_of_ge (radiusBranchGrid_norm_bound B D (a j) (b j) hD0 (hab j)
      (Z c i j ω) (hp c i j) hg t ht)) hbad
  calc
    _ ≤ ν.real (NotLip ∪ Nodes) := measureReal_mono hsub
    _ ≤ ν.real NotLip + ν.real Nodes := measureReal_union_le _ _
    _ = ν.real Nodes := by rw [hnull, zero_add]
    _ ≤ 2 * N * (∑ j, ((M j : ℝ)+1))*tail := hnodes
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (by positivity)) (Real.exp_pos _).le

end PaperFormalization.Manuscript
