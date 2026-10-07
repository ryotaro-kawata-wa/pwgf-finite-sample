import PaperFormalization.MatrixFactorization.SourceRadialCoercivity
import PaperFormalization.MatrixFactorization.AntisymmetricSourceFittingBound
import PaperFormalization.MatrixFactorization.SphericalCharacteristicEnergy
import PaperFormalization.MatrixFactorization.CharacteristicPointwiseRadial

/-! # Sharp source bounds along actual characteristics on a given cap interval

The branch identity is derived from the original initial reflection and the
stated uniqueness of characteristic laws. The transport differential bound
retains its full source remainder and imposes no current smallness condition.
The gradient-energy corollary uses the printed margin only at its evaluation
time. These results do not establish cap confinement or global flow existence.
-/
open MeasureTheory Set Filter
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- The original transport derivative has the sharp fitting remainder before
any initial or current smallness estimate is substituted. -/
theorem SphericalCharacteristicSolution.transport_deriv_le_source_remainder
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0)) (hp : 2 < p)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv X.transport t ≤ -2*lambda*(X.transport t)^(p/2) +
      2*sourceRadialConstant d O a teacher*(X.transport t)^2 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t htc
  have hlower := antisymmetricRadialObjectivePairing_lower_source O a hO pole radius lambda p hp
    (X.measure 0 t) (X.cap 0 t htc) teacher
  change deriv (fun s => productAntipodalTransportSq pole (X.measure 0 s) (X.measure 1 s)) t ≤ _
  rw [(X.productTransport_hasDerivAt hp t ht).deriv]
  simp only [Fin.sum_univ_two,SphericalCharacteristicSolution.transport,hb]
  change -2*antisymmetricRadialObjectivePairing O a pole lambda p (X.measure 0 t) teacher ≤ _
  linarith

/-- At a time satisfying the printed margin, the original squared gradient
obeys the exact source coefficient, also when transport is zero. -/
theorem SphericalCharacteristicSolution.gradientEnergy_lower_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp4 : p < 4)
    (t : Real) (ht : t ∈ Icc 0 T)
    (hsmall : sourceRadialConstant d O a teacher*(X.transport t)^((4-p)/2) ≤ lambda/2) :
    (lambda^2/4)*(X.transport t)^(p-1) ≤ X.gradientEnergy t := by
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t ht
  have hs : sourceRadialConstant d O a teacher*
      (productAntipodalTransportSq pole (X.measure 0 t)
        (reflectedMeasure (X.measure 0 t)))^((4-p)/2) ≤ lambda/2 := by
    simpa only [SphericalCharacteristicSolution.transport,hb] using hsmall
  have hg := antisymmetricGradientEnergy_lower_source O a hO pole radius lambda p hl hp hp4
    (X.measure 0 t) (X.cap 0 t ht) teacher hs
  simpa only [SphericalCharacteristicSolution.gradientEnergy,SphericalCharacteristicSolution.transport,
    Fin.sum_univ_two,hb,antisymmetricGradientEnergy] using hg

/-- The source Lfit controls each actual fitting field at every sphere point
on the given interval; the zero-distance case needs no division. -/
theorem SphericalCharacteristicSolution.fittingGradient_norm_le_transport_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (t : Real) (ht : t ∈ Icc 0 T) (i : Fin 2) (w : UnitSphere d) :
    norm (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i w) ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t) := by
  have hb := spherical_characteristic_antibranch_invariant hO X hunique hinitial t ht
  simpa only [SphericalCharacteristicSolution.transport,hb] using
    antisymmetric_sphericalFittingGradient_norm_source O a hO pole radius
      (X.measure 0 t) (X.cap 0 t ht) teacher i w

/-- The actual supported-particle half-cost has the sharp Lfit radial bound,
including particles at either pole. No radial differential premise is used. -/
theorem SphericalCharacteristicSolution.assignedCost_deriv_le_source
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (i : Fin 2) (w : UnitSphere d) (hw : w ∈ (initial i).support)
    (t : Real) (ht : t ∈ Ioo 0 T) :
    deriv (fun s => assignedCost pole (X.characteristic i s w)) t ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) -
      lambda*(X.transport t)^(p/2-1)*(sphericalPoleRadius pole (X.characteristic i t w))^2 := by
  have htc : t ∈ Icc (0 : Real) T := ⟨ht.1.le,ht.2.le⟩
  have hq : norm (assignedGradient pole (X.characteristic i t w)) =
      sphericalPoleRadius pole (X.characteristic i t w) :=
    assignedGradient_norm_on_support pole radius (X.measure i t) (X.cap i t htc)
      (X.characteristic i t w) (X.characteristic_mem_support i t htc w hw)
  have hfit := X.fittingGradient_norm_le_transport_source hO hunique hinitial t htc i
    (X.characteristic i t w)
  have hpair : -inner Real
      (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
        (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w)) ≤
      sourceFittingConstant d O a teacher*Real.sqrt (X.transport t)*
        sphericalPoleRadius pole (X.characteristic i t w) := by
    calc
      _ ≤ |inner Real
          (sphericalFittingGradient O a (X.measure 0 t) (X.measure 1 t) teacher teacher i
            (X.characteristic i t w)) (assignedGradient pole (X.characteristic i t w))| :=
        neg_le_abs _
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
