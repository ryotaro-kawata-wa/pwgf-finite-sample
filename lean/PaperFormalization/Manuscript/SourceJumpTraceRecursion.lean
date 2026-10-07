import PaperFormalization.Manuscript.SourceConditionalActualJump
import PaperFormalization.Manuscript.JumpForcing

/-! # Actual excluded jump failures give the tracking recursion

The first adapter only unpacks the already proved actual failure event. The
second records the exact observation/pretrace/posttrace/law identifications
needed to use it on a scheduled trajectory. The population law at the jump is
the pre-law, and no post-jump law is substituted for it. No desired scalar
recursion, Gaussian concentration premise, or new probability claim is added.
-/
open Matrix MeasureTheory Set
open scoped BigOperators NNReal Matrix.Norms.Frobenius
namespace PaperFormalization.Manuscript
variable {N d : ℕ} {S Ω : Type*}
variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℝ (H n)] [∀ n, CompleteSpace (H n)]

/-- Excluding the literal failure event yields its actual normalized jump
recursion once population eligibility and pre-particle localization hold. -/
theorem actual_source_jump_recursion_of_not_mem
    (c C g p q D : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (G : lp H 2 → ℝ) (L : ℝ≥0) (PopGood : Set S)
    (μ : S → Measure (EuclideanSpace ℝ (Fin d)))
    (X Y : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (Xpost Ypost : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (eta : ℕ → ℝ) (i : ℕ) (u : ℝ) (h : S) (ω : Ω)
    (hgood : (h,ω) ∉ actualSourceJumpFailure c C g p q D φ G L PopGood μ X Y Xpost Ypost (eta i) u)
    (hpop : h ∈ PopGood) (hX : ∀ j, ‖X h j‖ ≤ D) (hY : ∀ j, ‖Y h j‖ ≤ D) :
    let F := sourceWeightedFeatureMap c p φ
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L * sourceGaussianDeviation u
    let Gamma := momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun j => φ n (Y h j))) (fun n _ => ∫ z, φ n z ∂μ h) 0
    let GammaTilde := matrixNuclearValue (populationCovarianceResidual (μ h) (fun j => Y h j)
      (fun z => stackedKernelMatrix (fun j => actualMomentKernelMatrix F G (∫ z, F z ∂μ h) (Y h j) z))) / N
    ‖Xpost h ω-Ypost h ω‖/Real.sqrt N ≤
      (1+sourceJumpError A eta i)*(‖X h-Y h‖/Real.sqrt N) +
        sourceJumpForcing A eta (fun _ => Gamma) (fun _ => GammaTilde) i := by
  unfold actualSourceJumpFailure at hgood
  simp only [mem_setOf_eq] at hgood
  have hle := not_lt.mp (fun hbad => hgood ⟨⟨hpop,hX,hY⟩,hbad⟩)
  exact hle

/-- A point of the same original-system event yields the scheduled tracking
jump inequality after explicit actual pre/post particle and pre-law identity.
The scalar residuals are defined from that actual pre-law and actual pre-Y. -/
theorem actual_tracking_jump_recursion_of_observed_not_mem
    (c C g p q D : ℝ) (φ : ∀ n, EuclideanSpace ℝ (Fin d) → H n)
    (G : lp H 2 → ℝ) (L : ℝ≥0) (PopGood : Set S)
    (μview : S → Measure (EuclideanSpace ℝ (Fin d)))
    (Xview Yview : S → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (XpostView YpostView : S → Ω → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (etaView u : ℝ) (h : S) (ω : Ω)
    (tau eta : ℕ → ℝ) (X Y : ℝ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (preX preY : ℕ → PiLp 2 fun _ : Fin N => EuclideanSpace ℝ (Fin d))
    (muPre : ℕ → Measure (EuclideanSpace ℝ (Fin d))) (i : ℕ)
    (hgood : (h,ω) ∉ actualSourceJumpFailure c C g p q D φ G L
      PopGood μview Xview Yview XpostView YpostView etaView u)
    (hpop : h ∈ PopGood) (hX : ∀ j, ‖preX i j‖ ≤ D) (hY : ∀ j, ‖preY i j‖ ≤ D)
    (hpreX : Xview h = preX i) (hpreY : Yview h = preY i)
    (hpostX : XpostView h ω = X (tau (i+1))) (hpostY : YpostView h ω = Y (tau (i+1)))
    (hpreLaw : μview h = muPre i) (heta : etaView = eta i) :
    let F := sourceWeightedFeatureMap c p φ
    let A := sourceJumpCoefficient d (featureDisplacementLambda c C g p q D L) L * sourceGaussianDeviation u
    let r := fun t => ‖X t-Y t‖/Real.sqrt N
    let pre := fun j => ‖preX j-preY j‖/Real.sqrt N
    let GammaPre := fun j => momentResidual (featureResidualWeight c p L)
      (fun n _ => finiteFeatureMean (fun k => φ n (preY j k))) (fun n _ => ∫ z, φ n z ∂muPre j) 0
    let GammaTildePre := fun j => matrixNuclearValue (populationCovarianceResidual (muPre j) (fun k => preY j k)
      (fun z => stackedKernelMatrix (fun k => actualMomentKernelMatrix F G (∫ z, F z ∂muPre j) (preY j k) z))) / N
    r (tau (i+1)) ≤ (1+sourceJumpError A eta i)*pre i +
      sourceJumpForcing A eta GammaPre GammaTildePre i := by
  rw [heta] at hgood
  have hrec := actual_source_jump_recursion_of_not_mem c C g p q D φ G L PopGood μview
    Xview Yview XpostView YpostView eta i u h ω hgood hpop
    (by simpa only [hpreX] using hX) (by simpa only [hpreY] using hY)
  dsimp only at hrec ⊢
  simpa only [hpreX,hpreY,hpostX,hpostY,hpreLaw,sourceJumpForcing] using hrec
end PaperFormalization.Manuscript
