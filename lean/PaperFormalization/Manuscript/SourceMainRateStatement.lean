import PaperFormalization.Manuscript.SourceUniformCorollaryRates

/-! # Main-text pointwise rate with exact constants and both trace labels
M13t verified implementation. The confidence scale is N*(e+T)/p, NOT the
larger appendix Xi. The prefix in the pretrace forcing remains k. Integrability
is exported alongside each objective value bound. No rate of vanishing for an
arbitrary uncontrolled curvature path is asserted.
-/
open MeasureTheory Set
namespace PaperFormalization.Manuscript
variable {N d : Nat}
variable {H : Nat -> Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace Real (H n)] [∀ n, CompleteSpace (H n)]

def SourceJointRateConclusion
    (F : EuclideanSpace Real (Fin d) -> lp H 2) (G : lp H 2 -> Real)
    (law : Real -> Measure (EuclideanSpace Real (Fin d)))
    (preLaw : Nat -> Measure (EuclideanSpace Real (Fin d)))
    (X Y : Real -> SourceFiniteConfiguration N d)
    (preX preY : Nat -> SourceFiniteConfiguration N d)
    (kappa : Real -> Real) (tau eta : Nat -> Real)
    (J : Nat) (T confidence epsilon M : Real) : Prop :=
  (∀ t ∈ Icc 0 T, Integrable F (law t) ∧
    max (norm (X t-Y t)/Real.sqrt N) (sourceObjectiveError F G (law t) (X t)) ≤
      M*(sourceMainXi N T confidence)^epsilon*sourceAsymptoticProfile N J T kappa tau eta t) ∧
  (∀ k < J, Integrable F (preLaw k) ∧
    max (norm (preX k-preY k)/Real.sqrt N) (sourceObjectiveError F G (preLaw k) (preX k)) ≤
      M*(sourceMainXi N T confidence)^epsilon*
        sourceAsymptoticProfile N k T kappa tau eta (tau (k+1)))

end PaperFormalization.Manuscript
