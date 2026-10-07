import PaperFormalization.MatrixFactorization.SourceLocalGeometry

open MeasureTheory Set Filter
open scoped Topology
open PaperFormalization.MatrixFactorization

-- The model retains the original teacher probability and genuinely active
-- coefficients. These are standing data, rather than geometric conclusions.
example {d h : Nat} (M : SourceMFModel d h) : IsProbabilityMeasure M.teacher :=
  inferInstance

example {d h : Nat} (M : SourceMFModel d h) (hO : M.active.Nonempty) :
    ∃ n ∈ M.active, M.coefficient n ≠ 0 := by
  obtain ⟨n, hn⟩ := hO
  exact ⟨n, hn, M.active_nonzero n hn⟩

-- Both the zero activation and an actual nonzero degree-one activation
-- inhabit the standing model, including its original closed-support caps.
example {d : Nat} (pole : UnitSphere d) : Nonempty (SourceMFModel d 1) := by
  refine ⟨{
    active := ∅
    coefficient := fun _ => 0
    odd := ?_
    active_nonzero := ?_
    pole := pole
    radius := 1
    teacher := antipodalMeasure pole
    teacher_caps := antipodalMeasure_twoCap pole (by norm_num) ?_ }⟩
  · simp
  · simp
  · have := Real.pi_gt_three
    linarith

example {d : Nat} (pole : UnitSphere d) :
    ∃ M : SourceMFModel d 1, M.active = {1} := by
  let a : Nat → Weight 1 := fun _ => WithLp.toLp 2 (fun _ => (1 : Real))
  have ha (n : Nat) : a n ≠ 0 := by
    intro hzero
    have h := congrArg (fun x : Weight 1 => x (0 : Fin 1)) hzero
    norm_num [a] at h
  refine ⟨{
    active := {1}
    coefficient := a
    odd := ?_
    active_nonzero := ?_
    pole := pole
    radius := 1
    teacher := antipodalMeasure pole
    teacher_caps := antipodalMeasure_twoCap pole (by norm_num) ?_ }, rfl⟩
  · intro n hn
    have : n = 1 := by simpa using hn
    subst n
    decide
  · exact fun n _ => ha n
  · have := Real.pi_gt_three
    linarith

-- A noninteger exponent in the attraction range satisfies the complete
-- four-item theorem, including the original item-specific implications.
example {d h : Nat} (M : SourceMFModel d h) :
    MFLocalAttraction M 1 (5/2) ∧ MFAnnularCurvature M (5/2) ∧
      MFTransverseEscape M 1 (5/2) ∧ MFTeacherCurvature M 1 (5/2) :=
  source_mf_local_geometry M 1 (5/2) (by norm_num) (by norm_num)

-- The upper endpoint p<3 belongs only to attraction. The other curvature
-- items continue to cover p=4, with no accidental shared upper bound.
example {d h : Nat} (M : SourceMFModel d h) : MFAnnularCurvature M 4 :=
  source_mf_annular_curvature M 4 (by norm_num)

example {d h : Nat} (M : SourceMFModel d h) : MFTeacherCurvature M 1 4 :=
  source_mf_teacher_curvature M 1 4 (by norm_num) (by norm_num)

-- The transverse construction itself includes zero regularization, and the
-- stationary-center identity does not require a positive regularization.
example {d h : Nat} (M : SourceMFModel d h) : MFTransverseEscape M 0 (5/2) :=
  source_mf_transverse_escape M 0 (5/2) (by norm_num)

example {d h : Nat} (M : SourceMFModel d h) (i : Fin 2) (w : UnitSphere d) :
    sphericalObjectiveGradient M.active M.coefficient M.pole 0 (5/2)
      (antipodalMeasure M.pole) (antipodalMeasure M.pole) M.teacher M.teacher i w = 0 :=
  source_mf_center_stationary M 0 (5/2) (by norm_num) i w

-- The attraction assertion provides a positive basin and the two closed
-- source margins before an initial law or trajectory is supplied.
example {d h : Nat} (M : SourceMFModel d h) :
    ∃ zstar : Real, 0 < zstar ∧
      sourceRadialConstant d M.active M.coefficient M.teacher * zstar ^ ((4-(5/2 : Real))/2) ≤ 1/2 ∧
      (sourceFittingConstant d M.active M.coefficient M.teacher / 1) *
        zstar ^ ((3-(5/2 : Real))/2) ≤ M.radius/2 := by
  obtain ⟨zstar, hz, hrad, hforce, _⟩ :=
    source_mf_local_attraction M 1 (5/2) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨zstar, hz, hrad, hforce⟩

-- One neighborhood works for every nonzero product L2 direction and for
-- both actual paths. Positivity is derived from the common uniform margin.
example {d h : Nat} (M : SourceMFModel d h) (lambda p : Real)
    (hlambda : 0 < lambda) (hp : 2 < p)
    (hZo : 0 < productAntipodalTransportSq M.pole M.teacher M.teacher) :
    ∃ rho : Real, 0 < rho ∧ ∀ P : SphericalVariation d,
      P.pole = M.pole → P.radius = M.radius →
      sphericalWassersteinSq (P.measure 0) M.teacher +
        sphericalWassersteinSq (P.measure 1) M.teacher < rho^2 →
      0 < variationEnergy P →
      0 < deriv (deriv (variationObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0 ∧
      0 < deriv (deriv (variationRetractedObjective M.active M.coefficient P lambda p M.teacher M.teacher)) 0 := by
  obtain ⟨rho, c, hrho, hc, H⟩ := source_mf_teacher_curvature M lambda p hlambda hp hZo
  refine ⟨rho, hrho, ?_⟩
  intro P hpole hradius hnear hE
  have hb := H P hpole hradius hnear
  exact ⟨(mul_pos hc hE).trans_le hb.1, (mul_pos hc hE).trans_le hb.2⟩

-- The estimate bundle returned by attraction retains zero initial distance
-- and t=0; it identifies both original laws without claiming zero fit loss.
example {d h : Nat} (M : SourceMFModel d h) (lambda p : Real)
    (initial : Fin 2 → Measure (UnitSphere d))
    (X : PrimalACCharacteristicData M.active M.coefficient M.pole lambda p M.teacher initial)
    (H : PrimalACGlobalEstimates X)
    (hzero : productAntipodalTransportSq M.pole (initial 0) (initial 1) = 0) :
    ∀ i t, 0 ≤ t → X.measure i t = antipodalMeasure M.pole := by
  intro i t ht
  exact H.zero_laws 0 t (by norm_num) ht (by simpa only [X.transport_initial] using hzero) i
