import PaperFormalization.MatrixFactorization.SphericalSupportRadius
import PaperFormalization.MatrixFactorization.SphericalCharacteristicJointContinuity
import Mathlib.Topology.Order.Compact

/-! # Compact maximum radii under explicitly supported joint continuity

These are topological tools for the remaining continuation argument. Joint
continuity is an explicit input of the general lemma; this file does not
assert that a cap-free original WGF already satisfies it.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A continuous family on a fixed compact label set has a continuous exact
supremum on the given time set, without requiring continuity outside it. -/
theorem compact_continuousOn_sSup {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] {S : Set A} {K : Set B} (hK : IsCompact K)
    (F : A → B → Real) (hf : ContinuousOn (fun p : A × B => F p.1 p.2) (S ×ˢ K)) :
    ContinuousOn (fun t => sSup (F t '' K)) S := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hg : Continuous (fun p : S × K => F p.1.val p.2.val) := by
    apply hf.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    intro p
    exact ⟨p.1.property,p.2.property⟩
  have hc := (isCompact_univ : IsCompact (Set.univ : Set K)).continuous_sSup (f := fun (t : S) (w : K) => F t.val w.val) hg
  have he (t : S) : (fun w : K => F t.val w.val) '' univ = F t.val '' K := by
    ext y
    constructor
    · rintro ⟨w,_,rfl⟩
      exact ⟨w.val,w.property,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨⟨w,hw⟩,mem_univ _,rfl⟩
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun t : S => sSup (F t.val '' K))
  simpa only [he] using hc

/-- The exact maximum angular radius of all originally supported particles
at one time; this is independent of current law or cap membership. -/
noncomputable def supportedFlowRadius {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d) (t : Real) : Real :=
  max (sSup ((fun w => sphericalPoleRadius pole (Phi 0 t w)) '' (initial 0).support))
      (sSup ((fun w => sphericalPoleRadius pole (Phi 1 t w)) '' (initial 1).support))

/-- Supported joint continuity gives continuity of the literal two-support
maximum, the uniformity required by an eventual first-exit argument. -/
theorem supportedFlowRadius_continuousOn {d : Nat} (pole : UnitSphere d)
    (initial : Fin 2 → Measure (UnitSphere d))
    (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d) (S : Set Real)
    (hPhi : ∀ i, ContinuousOn (fun tw : Real × UnitSphere d => Phi i tw.1 tw.2)
      (S ×ˢ (initial i).support)) :
    ContinuousOn (supportedFlowRadius pole initial Phi) S := by
  have hc (i : Fin 2) : ContinuousOn
      (fun t => sSup ((fun w => sphericalPoleRadius pole (Phi i t w)) '' (initial i).support)) S :=
    compact_continuousOn_sSup (Measure.isClosed_support (μ := initial i)).isCompact
      (fun t w => sphericalPoleRadius pole (Phi i t w))
      ((sphericalPoleRadius_continuous pole).comp_continuousOn (hPhi i))
  exact (hc 0).sup (hc 1)

/-- On an already supplied cap interval, the required joint regularity and
therefore the exact supported maximum-radius continuity are derived from the
original characteristic ODE. This statement does not initialize a cap interval. -/
theorem SphericalCharacteristicSolution.supportedFlowRadius_continuousOn {d h : Nat}
    {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
    {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
    {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hp : 2 < p) :
    ContinuousOn (supportedFlowRadius pole initial X.characteristic) (Icc 0 T) :=
  MatrixFactorization.supportedFlowRadius_continuousOn pole initial X.characteristic
    (Icc 0 T) (X.characteristic_joint_continuousOn hp)

end PaperFormalization.MatrixFactorization
