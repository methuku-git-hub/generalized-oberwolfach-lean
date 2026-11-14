module

public import Oberwolfach.TypedMarkedRestrictionLoads
public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.MarkedSpokeResiduals

@[expose] public section

/-! The fixed normalized coefficient of a successor tuple gives exact load
identities in the actual sampled host, with both spoke types distinguished. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_seed_rim_load
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>weight W.1.val/(D*p^m*k*s₀^m)
    ∀ e:E⊕K,typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H
      (Sum.inl (Sum.map Subtype.val Subtype.val e))=markedWheelRimLoad ψ e:=by
  intro E K seed ψ e
  have hh:=typedMarkedPotentialLoad_restricted_rim
    (tail:=(Prod.fst:V×V→V)) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd)
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false xy.1 xy.2=1)
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true xy.1 xy.2=1)
    (fun _ _ h=>h) (fun _ _ h=>h)
    (H₀':=H false) (HK':=H true) (fun _ _ _=>True.intro) (fun _ _ _=>True.intro) seed e
  have hH:(fun j v u=>if j then H true v u else H false v u)=H:=by
    funext j v u;cases j <;> rfl
  rw [hH] at hh
  exact hh

theorem marked_sample_seed_spoke_load
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>weight W.1.val/(D*p^m*k*s₀^m)
    ∀ j v u,H j v u→typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H
      (Sum.inr (j,v,u))=markedWheelSpokeLoad ψ j v u:=by
  intro E K seed ψ j v u he
  have he':if j then H true v u else H false v u:=by cases j <;> exact he
  have hh:=typedMarkedPotentialLoad_restricted_spoke
    (tail:=(Prod.fst:V×V→V)) (head:=Prod.snd) (ktail:=Prod.fst) (khead:=Prod.snd)
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false xy.1 xy.2=1)
    (fun xy=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true xy.1 xy.2=1)
    (fun _ _ h=>h) (fun _ _ h=>h)
    (H₀':=H false) (HK':=H true) (fun _ _ _=>True.intro) (fun _ _ _=>True.intro) seed j v u he'
  have hH:(fun j v u=>if j then H true v u else H false v u)=H:=by
    funext j v u;cases j <;> rfl
  rw [hH] at hh
  exact hh

end Oberwolfach
