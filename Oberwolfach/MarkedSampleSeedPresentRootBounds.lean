module

public import Oberwolfach.MarkedSampleSeedLoadIdentities

@[expose] public section

/-! Actual-load bounds require the potential estimate only at retained
roots. In particular, no estimate is requested at a deleted spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_seed_present_root_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀ η:ℝ) (hη:0≤η)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>weight W.1.val/(D*p^m*k*s₀^m)
    (∀ e:E⊕K,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H
      (Sum.inl (Sum.map Subtype.val Subtype.val e))-1|≤η)→
    (∀ j v u,H j v u→|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H (Sum.inr (j,v,u))-1|≤η)→
    (∀ e,|markedWheelRimLoad ψ e-1|≤η)∧(∀ j v u,|markedSpokeResidual ψ j v u|≤η):=by
  intro E K seed ψ hR hS
  constructor
  · intro e
    rw [←marked_sample_seed_rim_load P π d m D p k s₀ weight σ H e]
    exact hR e
  · intro j v u
    by_cases he:if j then H true v u else H false v u
    · have he':H j v u:=by cases j <;> exact he
      rw [markedSpokeResidual,if_pos he,abs_sub_comm,
        ←marked_sample_seed_spoke_load P π d m D p k s₀ weight σ H j v u he']
      exact hS j v u he'
    · rw [markedSpokeResidual_outside ψ j v u he,abs_zero]
      exact hη

end Oberwolfach
