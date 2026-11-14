module

public import Oberwolfach.LongAssignedMarkedPhysicalDeletion
public import Oberwolfach.LongAssignedOrdinaryPhysicalDeletion

@[expose] public section
/-! A single fixed raw state supplies the adaptive rim-deletion estimate
for every marked or ordinary component of the assigned mixed seed family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_mixed_seed_load_after_physical_deletion
    (hn:0<n) (hu:Fintype.card U≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (hm:3≤m) (θ D:ℝ) (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (hBM:0≤BM) (hBO:∀i,0≤BO i)
    (hwM:∀W,0≤longAssignedMarkedSeed F hF K m d θ D π weight W ∧
      longAssignedMarkedSeed F hF K m d θ D π weight W≤BM/(n:ℝ)^m)
    (hwO:∀i W,0≤longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W ∧
      longAssignedOrdinarySeed F hF K m d θ D P π ni hni w i W≤BO i/(n:ℝ)^(ni i+1))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let survived:=fun z=>decide (z∈S)
    ∀(i:Option (Fin K)) (root:LongRawHubResource n U) (target:ℝ),
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root state-target|+
        match i with
        | none => 10*δ*((m:ℝ)+1)^4*BM/(n:ℝ)
        | some i => 10*δ*((ni i:ℝ)+2)^4*BO i/(n:ℝ) :=by
  intro ℓ Wm Wo W R state S survived i root target
  cases i with
  | none =>
    have h:=long_assigned_marked_seed_load_after_physical_deletion (K:=K) hn hu F hF m d hm θ D P Del π
      weight BM hBM hwM raw g j δ hDel root target
    dsimp only at h
    have hR:R none=typedMarkedOccurrenceResources:=by
      funext C
      dsimp [R,longRawHubResources,longRawSeedResources,longMixedSeedResources]
      congr 3 <;> exact Subsingleton.elim _ _
    have hW:W none=Wm:=by rfl
    rw [hR,hW]
    exact h
  | some i =>
    have h:=long_assigned_ordinary_seed_load_after_physical_deletion hn hu F hF m d θ D P Del π
      ni hni w BO hBO hwO raw g j δ hDel i root target
    dsimp [R,longRawHubResources,longRawSeedResources,longMixedSeedResources,W,longMixedSeedWeight,Wm,Wo,ℓ]
    dsimp only at h
    exact h
end Oberwolfach
