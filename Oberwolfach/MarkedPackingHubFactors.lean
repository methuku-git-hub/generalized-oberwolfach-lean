module

public import Oberwolfach.MarkedHubFactorLift

@[expose] public section
/-! Extract the vertex-disjoint factor at each hub from a physical marked
wheel packing that covers exactly the prescribed spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def markedWheelAtHub (u:U) (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hu:W.2.val=u):
    HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u := by
  rcases W with ⟨C,⟨w,hw⟩⟩
  dsimp at hu
  subst w
  exact ⟨C.val,C.property,hw⟩

theorem markedWheelAtHub_val (u:U) (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hu:W.2.val=u):
    (markedWheelAtHub u W hu).val=W.1.val := by
  rcases W with ⟨C,⟨w,hw⟩⟩
  dsimp at hu
  subst w
  rfl

theorem hubCycleWheel_markedWheelAtHub (u:U) (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hu:W.2.val=u):
    hubCycleWheel u (markedWheelAtHub u W hu)=W := by
  rcases W with ⟨C,⟨w,hw⟩⟩
  dsimp at hu
  subst w
  rfl

theorem marked_packing_to_hub_factors
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hP:∀W∈P,∀Z∈P,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hspoke:∀v u,Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources ↔ H₀ v u∨Hₖ v u):
    ∀u:U,∃M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u),
      (∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D)) ∧
      M.biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u) ∧
      M.image (hubCycleWheel u)=P.filter (fun W=>W.2.val=u) := by
  intro u
  let M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u):=
    Finset.univ.filter (fun C=>hubCycleWheel u C∈P)
  have hmember:∀C,C∈M↔hubCycleWheel u C∈P:=by intro C;simp [M]
  refine ⟨M,?_,?_,?_⟩
  · intro C hC D hD hCD
    have hne:hubCycleWheel u C≠hubCycleWheel u D:=fun he=>hCD (Subtype.ext (congrArg (fun W=>W.1.val) he))
    have hd:=hP (hubCycleWheel u C) ((hmember C).mp hC) (hubCycleWheel u D) ((hmember D).mp hD) hne
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have h1:Sum.inr (v,u)∈markedWheelPhysicalResources (hubCycleWheel u C):=by
      apply (markedWheelPhysicalResources_spoke _ v u).2
      exact ⟨rfl,hv⟩
    have h2:Sum.inr (v,u)∈markedWheelPhysicalResources (hubCycleWheel u D):=by
      apply (markedWheelPhysicalResources_spoke _ v u).2
      exact ⟨rfl,hw⟩
    exact Finset.disjoint_left.mp hd h1 h2
  · ext v
    simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨C,hC,hv⟩
      apply (hspoke v u).1
      refine Finset.mem_biUnion.mpr ⟨hubCycleWheel u C,(hmember C).mp hC,?_⟩
      exact (markedWheelPhysicalResources_spoke _ v u).2 ⟨rfl,hv⟩
    · intro hv
      have hs:Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources:=(hspoke v u).2 hv
      obtain ⟨W,hW,hvW⟩:=Finset.mem_biUnion.mp hs
      obtain ⟨hu,hvW⟩:=(markedWheelPhysicalResources_spoke W v u).1 hvW
      let C:=markedWheelAtHub u W hu
      have he:hubCycleWheel u C=W:=hubCycleWheel_markedWheelAtHub u W hu
      refine ⟨C,(hmember C).2 (by rw [he];exact hW),?_⟩
      change v∈Finset.univ.image C.val
      rw [show C.val=W.1.val from markedWheelAtHub_val u W hu]
      exact hvW
  · ext W
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨C,hC,rfl⟩
      exact ⟨(hmember C).mp hC,rfl⟩
    · rintro ⟨hW,hu⟩
      let C:=markedWheelAtHub u W hu
      have he:hubCycleWheel u C=W:=hubCycleWheel_markedWheelAtHub u W hu
      exact ⟨C,(hmember C).2 (by rw [he];exact hW),he⟩
end Oberwolfach
