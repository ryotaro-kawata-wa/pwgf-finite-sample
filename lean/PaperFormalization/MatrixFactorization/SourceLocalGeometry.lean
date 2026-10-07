import PaperFormalization.MatrixFactorization.SourceLocalGeometryStatements

/-! # MF48: the four-item source local geometry theorem

Each proof applies the verified original-model result with the model's exact
standing restrictions. The result does not postulate a connecting trajectory
or a sampled controlled-curvature condition, which the source also excludes.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

/-- A common positive source basin gives the original same-trajectory
attraction and energy conclusions in the confirmed AC characteristic class. -/
theorem source_mf_local_attraction {d h : Nat} (M : SourceMFModel d h)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) : MFLocalAttraction M lambda p := by
  intro hp3
  obtain ⟨zstar, hzstar, hrad, hforce⟩ := source_basin_exists M.active M.coefficient M.teacher
    M.radius lambda p M.teacher_caps.radius_pos hlambda hp hp3
  refine ⟨zstar, hzstar, hrad, hforce, ?_⟩
  intro initial X hX hu hi hc hinit
  obtain ⟨hB, hbranch, hsupport, hcaps, hcurrent, H, hZ, hsqrt, hcomponent,
    hmom, hodd, hS, hA, henergy, hzero⟩ :=
    source_l2_ac_global_attraction X M.odd hX hu hi M.radius hc hlambda hp hp3
      zstar hzstar hrad hforce hinit
  exact ⟨hB, hbranch, hsupport, hcaps, hcurrent, H, hZ, hsqrt, hcomponent,
    hmom, hodd, hS, hA, henergy, hzero,
    source_l2_ac_integrated_energy X M.odd hX hu hi M.radius hc hlambda hp hp3
      zstar hzstar hrad hforce hinit⟩

/-- The actual source model satisfies the uniformly quantified annular item. -/
theorem source_mf_annular_curvature {d h : Nat} (M : SourceMFModel d h)
    (p : Real) (hp : 2 < p) : MFAnnularCurvature M p := by
  intro zeta hzeta
  obtain ⟨L, hL, H⟩ := source_annular_uniform M.active M.odd M.coefficient M.teacher
    M.radius zeta p M.teacher_caps.radius_pos M.teacher_caps.radius_lt hzeta hp
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda P _hpole hradius hbranch hZ hE
  exact H lambda hlambda P hradius hbranch hZ hE

/-- Nonempty active support and the original sliced imbalance supply the
same smooth transverse escape path; a positive signal is not an input. -/
theorem source_mf_transverse_escape {d h : Nat} (M : SourceMFModel d h)
    (lambda p : Real) (hp : 2 < p) : MFTransverseEscape M lambda p := by
  intro hactive e rvis gamma himb
  obtain ⟨n, hn⟩ := hactive
  exact source_imbalance_transverse_escape M.active M.coefficient M.odd
    ⟨n, hn, M.active_nonzero n hn⟩ M.pole M.radius M.teacher_caps.radius_pos
    M.teacher_caps.radius_lt M.teacher e rvis gamma himb lambda p hp

/-- The same radius and margin control EXP and normalized second variations
near the original teacher, without assuming that it is stationary. -/
theorem source_mf_teacher_curvature {d h : Nat} (M : SourceMFModel d h)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) : MFTeacherCurvature M lambda p := by
  intro hZo
  obtain ⟨rho, c, hrho, hc, H⟩ := normalized_teacher_neighborhood_curvature
    M.active M.coefficient M.pole M.radius M.teacher M.teacher_caps lambda p hlambda hp hZo
  refine ⟨rho, c, hrho, hc, ?_⟩
  intro P hpole hradius hnear
  have hb := H P hpole hradius hnear
  refine ⟨?_, hb⟩
  rwa [(variationRetractedObjective_derivatives_eq_exp M.active M.coefficient P
    lambda p hlambda hp M.teacher M.teacher).2] at hb

/-- The four items of `prop:mf-local-geometry`, on the original finite odd
model and the author-confirmed intrinsic AC characteristic interpretation.
Each additional item-specific condition remains inside its own conclusion. -/
theorem source_mf_local_geometry {d h : Nat} (M : SourceMFModel d h)
    (lambda p : Real) (hlambda : 0 < lambda) (hp : 2 < p) :
    MFLocalAttraction M lambda p ∧ MFAnnularCurvature M p ∧
      MFTransverseEscape M lambda p ∧ MFTeacherCurvature M lambda p :=
  ⟨source_mf_local_attraction M lambda p hlambda hp,
    source_mf_annular_curvature M p hp,
    source_mf_transverse_escape M lambda p hp,
    source_mf_teacher_curvature M lambda p hlambda hp⟩

/-- The antipodal target is stationary for the same full objective field. -/
theorem source_mf_center_stationary {d h : Nat} (M : SourceMFModel d h)
    (lambda p : Real) (hp : 2 < p) (i : Fin 2) (w : UnitSphere d) :
    sphericalObjectiveGradient M.active M.coefficient M.pole lambda p
      (antipodalMeasure M.pole) (antipodalMeasure M.pole) M.teacher M.teacher i w = 0 :=
  sphericalObjectiveGradient_antipodal M.active M.coefficient M.odd M.pole lambda p hp
    M.teacher M.teacher i w

end PaperFormalization.MatrixFactorization
