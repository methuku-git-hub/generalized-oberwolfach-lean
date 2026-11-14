module

public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! The chosen-vortex theorem's retained outcome is the same sigma-law input
used by the joint approximate/reference sampling theorem. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_retained_reference_principle
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a:Γ)
    (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀ u j,0≤q u j) (hQ:∀ u,∑ j,q u j≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ j,q u j))
    (Ref:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop)
    (hChosen:∀ E:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop,
      (99:ℝ)/100≤(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability E→
      ∃ z,0<(rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).mass z ∧ E z ∧ Ref z):
    let F:=fun σ:RawMarkedOutcome V U Γ Color=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
    let ν:=fun σ:RawMarkedOutcome V U Γ Color=>
      startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)) (startRetentionMinimum_le _);
    ∀ E:(Σ σ,F σ)→Prop,
      (99:ℝ)/100≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS)).sigma ν).probability E→
      ∃ z,Ref z ∧ E z:=by
  intro F ν E hE
  have hh:=hChosen E hE
  obtain ⟨z,_,hEz,hRz⟩:=hh
  exact ⟨z,hRz,hEz⟩
end Oberwolfach
