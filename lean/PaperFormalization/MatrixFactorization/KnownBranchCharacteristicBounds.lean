import PaperFormalization.MatrixFactorization.SourceCharacteristicRadial

/-! # MF23: sharp interval bounds from a previously established branch identity

Execution records: `MF23_VALIDATION.md`.

These are adapters, not new assumptions of a claimed
source theorem. The global represented-flow endpoint supplies `hb` by applying
GLOBAL uniqueness to a reflected GLOBAL flow. No implication from global
uniqueness to uniqueness of arbitrary finite-interval solutions is used.
The original cap-interval record and every verified predecessor are unchanged.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Sharp radial remainder on the actual laws, with branch supplied separately. -/
theorem SphericalCharacteristicSolution.transport_remainder_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hp : 2 < p) (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    deriv X.transport t ≤ -2*lambda*(X.transport t)^(p/2) +
      2*sourceRadialConstant d O a teacher*(X.transport t)^2 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hbranch := hb t htc
  have hlower := antisymmetricRadialObjectivePairing_lower_source O a hO pole radius lambda p hp
    (X.measure 0 t) (X.cap 0 t htc) teacher
  change deriv (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s)) t ≤ _
  rw [(X.productTransport_hasDerivAt hp t ht).deriv]
  simp only [Fin.sum_univ_two,SphericalCharacteristicSolution.transport,hbranch]
  change -2*antisymmetricRadialObjectivePairing O a pole lambda p (X.measure 0 t) teacher ≤ _
  linarith

/-- The existing sharp static energy bound needs the branch, not finite uniqueness. -/
theorem SphericalCharacteristicSolution.gradientEnergy_source_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (hsmall : sourceRadialConstant d O a teacher*(X.transport t)^((4-p)/2) ≤ lambda/2) :
    (lambda^2/4)*(X.transport t)^(p-1) ≤ X.gradientEnergy t := by
  have hbranch := hb t ht
  have hs : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (X.measure 0 t)
        (reflectedMeasure (X.measure 0 t)))^((4-p)/2) ≤ lambda/2 := by
    simpa only [SphericalCharacteristicSolution.transport,hbranch] using hsmall
  have hg := antisymmetricGradientEnergy_lower_source O a hO pole radius lambda p hl hp hp4
    (X.measure 0 t) (X.cap 0 t ht) teacher hs
  simpa only [SphericalCharacteristicSolution.gradientEnergy,SphericalCharacteristicSolution.transport,
    Fin.sum_univ_two,hbranch,antisymmetricGradientEnergy] using hg

/-- The literal source Lfit estimate is evaluated on the same current laws. -/
theorem SphericalCharacteristicSolution.fitting_bound_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (t : Real) (ht : t ∈ Icc (0 : Real) T) (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w) ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t) := by
  simpa only [SphericalCharacteristicSolution.transport,hb t ht] using
    antisymmetric_sphericalFittingGradient_norm_source O a hO pole radius
      (X.measure 0 t) (X.cap 0 t ht) teacher i w

/-- Both poles are included, because the differentiated object is the half-cost. -/
theorem SphericalCharacteristicSolution.particle_cost_bound_of_branch
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hb : ∀ t ∈ Icc (0 : Real) T, X.measure 1 t = reflectedMeasure (X.measure 0 t))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
    deriv (fun s => assignedCost pole (X.characteristic i s w)) t ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) -
      lambda*(X.transport t)^(p/2-1)*(sphericalPoleRadius pole (X.characteristic i t w))^2 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hq : norm (assignedGradient pole (X.characteristic i t w)) =
      sphericalPoleRadius pole (X.characteristic i t w) :=
    assignedGradient_norm_on_support pole radius (X.measure i t) (X.cap i t htc)
      (X.characteristic i t w) (X.characteristic_mem_support i t htc w hw)
  have hfit := X.fitting_bound_of_branch hO hb t htc i (X.characteristic i t w)
  have hpair : -inner Real
      (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
        (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w)) ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) := by
    calc
      _ ≤ |inner Real
          (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
            (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w))| := neg_le_abs _
      _ ≤ _ := (abs_real_inner_le_norm _ _).trans (by
        rw [← hq]
        exact mul_le_mul_of_nonneg_right hfit (norm_nonneg _))
  rw [(X.assignedCost_hasDerivAt i w hw t ht).deriv]
  simp only [sphericalObjectiveGradient,inner_add_left,metricGradient,
    real_inner_smul_left,real_inner_self_eq_norm_sq,hq]
  change -(_ + lambda*(X.transport t)^(p/2-1)*
    (sphericalPoleRadius pole (X.characteristic i t w))^2) ≤ _
  linarith

end PaperFormalization.MatrixFactorization
