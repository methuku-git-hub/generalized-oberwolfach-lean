module

public import Oberwolfach.MarkedRetainedReferencePrinciple
public import Oberwolfach.ExpandedReferencePositiveExtension

@[expose] public section
/-! A chosen-vortex reference outcome can be extended to a positive-mass
outcome of the dependent approximate/reference experiment. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_reference_positive_extension
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a:Γ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ v j,0≤q v j) (hQ:∀ v,∑ j,q v j≤1/8)
    (s:U→Color→ℝ) (hs:∀ v j,0≤s v j)
    (hS:∀ v,∑ j,s v j ≤ intervalUncoveredProbability d (∑ j,q v j))
    (Ref:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop)
    (hChosen:∀ E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop,
      (99:ℝ)/100≤(rawMarkedRetentionLaw π d hd a p k hp hk (by linarith) q hq hQ s hs hS).probability E→
      ∃ z,0<(rawMarkedRetentionLaw π d hd a p k hp hk (by linarith) q hq hQ s hs hS).mass z ∧ E z ∧ Ref z):
    let F:=fun σ:RawMarkedOutcome V U Γ Color=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
    let ν:=fun σ:RawMarkedOutcome V U Γ Color=>
      startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)) (startRetentionMinimum_le _)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let law:=μ.sigma (fun ω=>ν (f ω));
    ∀ Good:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))→Prop,
      (99:ℝ)/100≤law.probability Good→
      ∃ z,Ref ⟨f z.1,z.2⟩ ∧ Good z ∧ 0<law.mass z:=by
  intro F ν μ f law Good hGood
  have hRef:=marked_retained_reference_principle π d hd a p k hp hk (by linarith) q hq hQ s hs hS Ref hChosen
  exact raw_expanded_reference_positive_extension p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν Ref Good hGood hRef
end Oberwolfach
