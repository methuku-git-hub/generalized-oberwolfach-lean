module

public import Oberwolfach.MixedClassActualRetention
public import Oberwolfach.MarkedExpandedRetainedProjection

@[expose] public section
/-! The marked branch of the mixed experiment has exactly the retained
reference law; the ordinary branch has no extra random choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem mixed_class_marked_retention_projection
    (π:Equiv.Perm V) (a:Bool)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (E:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d a→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    (μ.sigma (mixedClassActualRetention true π d a)).probability
      (fun z=>E ⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩)=
    (rawMarkedRetentionLaw π d hd a p k hp hk (by linarith) q hq hQ s hs hS).probability E :=by
  intro μ
  let F:=fun σ:RawMarkedOutcome V U Bool Bool=>
    StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
  let ν:=fun σ:RawMarkedOutcome V U Bool Bool=>
    startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)) (startRetentionMinimum_le _)
  have h:=raw_expanded_marked_retained_projection_probability p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν E
  change (μ.sigma (fun ω=>ν (fun e=>rawExpandedMarkedCollapse e (ω e)))).probability
      (fun z=>E ⟨(fun e=>rawExpandedMarkedCollapse e (z.1 e)),z.2⟩)=
    ((FiniteLaw.pi (rawMarkedWheelLaw p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E
  exact h
end Oberwolfach
