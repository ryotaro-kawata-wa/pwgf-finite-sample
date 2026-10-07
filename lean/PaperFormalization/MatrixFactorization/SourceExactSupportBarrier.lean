import PaperFormalization.MatrixFactorization.ExactSupportRadius
import PaperFormalization.MatrixFactorization.SourceCharacteristicSupportClosure

/-! # The literal source maximum-radius barrier on the given cap interval

R0 is the maximum of the two actual support suprema, and Rbar is exactly the
source maximum of R0 and its forcing scale. The result controls original
supported particles and complete current supports. It does not extend the
time domain or assume a cap-free global characteristic representation.
-/
open MeasureTheory Set
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false
variable {d h : Nat} {O : Finset Nat} {a : Nat → Weight h} {pole : UnitSphere d}
  {radius lambda p : Real} {teacher : Measure (UnitSphere d)}
  {initial : Fin 2 → Measure (UnitSphere d)} {T : Real}

/-- Both printed basin margins imply the displayed source support bound with
the literal maximum/supremum R0, and give an actual smaller current cap class. -/
theorem SphericalCharacteristicSolution.support_exact_source_barrier
    (X : SphericalCharacteristicSolution O a pole radius lambda p teacher initial T)
    [IsProbabilityMeasure teacher] (hO : ∀ n ∈ O, Odd n)
    (hunique : SphericalCharacteristicLawUnique O a pole radius lambda p teacher initial T)
    (hinitial : initial 1 = reflectedMeasure (initial 0))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (_hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ radius/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    let Rbar := max (productSphericalSupportRadius pole initial)
      ((sourceFittingConstant d O a teacher/lambda)*
        (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
    Rbar < radius ∧
    (∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) ≤ Rbar) ∧
    (∀ t ∈ Icc (0 : Real) T,
      (∀ i : Fin 2, (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ Rbar}) ∧
      productSphericalSupportRadius pole (fun i => X.measure i t) ≤ Rbar ∧
      (∀ i : Fin 2, TwoCapClass pole ((Rbar+radius)/2) (X.measure i t))) := by
  let R0 := productSphericalSupportRadius pole initial
  let Rbar := max R0 ((sourceFittingConstant d O a teacher/lambda)*
    (productAntipodalTransportSq pole (initial 0) (initial 1))^((3-p)/2))
  have hR0 := X.initial_exact_support_radius
  have hr := (X.cap 0 0 ⟨le_rfl,X.time_nonneg⟩).radius_pos
  have hZ0 : 0 ≤ productAntipodalTransportSq pole (initial 0) (initial 1) := by
    rw [← X.transport_initial]
    exact X.productTransport_nonneg 0 ⟨le_rfl,X.time_nonneg⟩
  have hm := source_basin_initial_margins O a teacher lambda p radius zstar
    (productAntipodalTransportSq pole (initial 0) (initial 1)) hl hp3 hZ0 hinit hrad hforce
  have hRbar : Rbar < radius := max_lt hR0.2.1 (hm.2.trans_lt (by linarith))
  have hRbar0 : 0 ≤ Rbar := hR0.1.trans (le_max_left _ _)
  have hparticle : ∀ i w, w ∈ (initial i).support → ∀ t ∈ Icc (0 : Real) T,
      sphericalPoleRadius pole (X.characteristic i t w) ≤ Rbar := by
    intro i w hw t ht
    exact X.particle_radius_le_source_barrier hO hunique hinitial hl hp hp3 hm.1
      R0 hR0.1 hR0.2.2.1 i w hw t ht
  have hs : ∀ i t, t ∈ Icc (0 : Real) T →
      (X.measure i t).support ⊆ {w | sphericalPoleRadius pole w ≤ Rbar} := by
    intro i t ht
    exact X.support_radius_le_source_barrier hO hunique hinitial hl hp hp3 hm.1
      R0 hR0.1 hR0.2.2.1 i t ht
  refine ⟨hRbar,hparticle,?_⟩
  intro t ht
  refine ⟨fun i => hs i t ht,?_,?_⟩
  · exact ((productSphericalSupportRadius_cap_properties pole radius
      (fun i => X.measure i t) (fun i => X.cap i t ht)).2.2.2 Rbar).mpr
      (fun i w hw => hs i t ht hw)
  · intro i
    exact (X.cap i t ht).refine_radius_of_le Rbar ((Rbar+radius)/2)
      (by linarith) (by linarith) (by linarith) (hs i t ht)

end PaperFormalization.MatrixFactorization
