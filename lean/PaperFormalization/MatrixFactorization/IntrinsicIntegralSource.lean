import PaperFormalization.MatrixFactorization.IntrinsicACSourceClass
import PaperFormalization.MatrixFactorization.IntrinsicACGlobalAttraction

/-! # MF30: the actual integral source constructor belongs to the source class

The source L2 witness is retained by the MF28 constructor with the same laws,
paths and gradient. This closes the membership input for that constructor;
no new intrinsic first-variation premise is requested afterward.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace PaperFormalization.MatrixFactorization
set_option autoImplicit false

variable {d h : Nat} (O : Finset Nat) (a : Nat → Weight h)
  (pole : UnitSphere d) (lambda p : Real) (teacher : Measure (UnitSphere d))
  (initial : Fin 2 → Measure (UnitSphere d))
  (hprob : ∀ i, IsProbabilityMeasure (initial i))
  (Phi : Fin 2 → Real → UnitSphere d → UnitSphere d)
  (hPhiM : ∀ i t, Measurable (Phi i t))
  (hPhiC : ∀ i t, 0 ≤ t → ContinuousOn (Phi i t) (initial i).support)
  (hPhi0 : ∀ i w, w ∈ (initial i).support → Phi i 0 w = w)
  (g : Fin 2 → Real → UnitSphere d → Weight d)
  (hgM : ∀ i t, Measurable (g i t))
  (hgPhiM : ∀ i, Measurable (fun tw : Real × UnitSphere d => g i tw.1 (Phi i tw.1 tw.2)))
  (hfirst : ∀ᵐ t ∂volume.restrict (Ici (0 : Real)), ∀ i,
    ∃ G : sphereTangentL2 ((initial i).map (Phi i t)),
      HasSphereL2FirstVariation ((initial i).map (Phi i t))
        (sourcePartialObjective O a pole lambda p
          (fun j => (initial j).map (Phi j t)) teacher i) G ∧
      sphereL2Representative G =ᵐ[(initial i).map (Phi i t)] g i t)
  (hintegral : ∀ i (n : Nat), ∀ᵐ w ∂initial i,
    ∀ t ∈ Icc (0 : Real) n,
      (Phi i t w).val = (Phi i 0 w).val - ∫ r in 0..t, g i r (Phi i r w))

/-- Membership is supplied by the original L2 identity, on the unchanged laws. -/
theorem primalACOfIntegralL2_hasSource [IsProbabilityMeasure teacher]
    (hl : 0 ≤ lambda) (hp : 2 < p) :
    (primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl hp).HasSourceL2FirstVariation :=
  hfirst

/-- End-to-end application on the original integral characteristics. The
source-class membership, AC conversion, reflected competitor, and all-time
confinement are constructed internally. The returned laws are the supplied
pushforwards, and the energy uses the supplied measurable gradient. -/
theorem integral_l2_global_attraction [IsProbabilityMeasure teacher]
    (hO : ∀ n ∈ O, Odd n)
    (hu : SourceL2ACLawUnique O a pole lambda p teacher initial)
    (hi : initial 1 = reflectedMeasure (initial 0))
    (r : Real) (hc : ∀ i, TwoCapClass pole r (initial i))
    (hl : 0 < lambda) (hp : 2 < p) (hp3 : p < 3)
    (zstar : Real) (hzstar : 0 < zstar)
    (hrad : sourceRadialConstant d O a teacher*zstar^((4-p)/2) ≤ lambda/2)
    (hforce : (sourceFittingConstant d O a teacher/lambda)*zstar^((3-p)/2) ≤ r/2)
    (hinit : productAntipodalTransportSq pole (initial 0) (initial 1) ≤ zstar) :
    let X := primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl.le hp
    X.sourceBarrier < r ∧
    (∀ i w, w ∈ (initial i).support → ∀ t : Real, 0 ≤ t →
      sphericalPoleRadius pole (Phi i t w) ≤ X.sourceBarrier) ∧
    (∀ i t, 0 ≤ t → TwoCapClass pole r ((initial i).map (Phi i t))) ∧
    PrimalACGlobalEstimates X ∧
    Tendsto (fun t => productAntipodalTransportSq pole
      ((initial 0).map (Phi 0 t)) ((initial 1).map (Phi 1 t))) atTop (𝓝 0) ∧
    (∀ i n, Tendsto (fun t => rawMoment ((initial i).map (Phi i t)) n) atTop
      (𝓝 (rawMoment (antipodalMeasure pole) n))) ∧
    (∀ᵐ t ∂volume.restrict (Ioi (0 : Real)),
      (∀ i, Integrable (fun w => norm (g i t w)^2) ((initial i).map (Phi i t))) ∧
      HasDerivAt X.objective
        (-(∑ i : Fin 2, ∫ w, norm (g i t w)^2 ∂((initial i).map (Phi i t)))) t ∧
      deriv X.objective t ≤ -(lambda^2/4)*(X.transport t)^(p-1) ∧
      (0 < X.transport t → deriv X.objective t < 0)) := by
  let X := primalACOfIntegralL2 O a pole lambda p teacher initial hprob Phi
    hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl.le hp
  have hX : X.HasSourceL2FirstVariation :=
    primalACOfIntegralL2_hasSource O a pole lambda p teacher initial hprob Phi
      hPhiM hPhiC hPhi0 g hgM hgPhiM hfirst hintegral hl.le hp
  obtain ⟨hB, _, hsupport, hcaps, _, H, hZ, _, _, hmom, _, _, _, henergy, _⟩ :=
    source_l2_ac_global_attraction X hO hX hu hi r hc hl hp hp3 zstar hzstar hrad hforce hinit
  exact ⟨hB, hsupport, hcaps, H, hZ, hmom, henergy⟩

end PaperFormalization.MatrixFactorization
