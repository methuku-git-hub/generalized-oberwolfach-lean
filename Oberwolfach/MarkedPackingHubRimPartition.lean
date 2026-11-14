module

public import Oberwolfach.MarkedPackingHubFactors

@[expose] public section
/-! Hub factors extracted from a physical marked wheel packing have disjoint
rim edges across hubs and cover exactly the packing's physical rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem marked_packing_hub_rim_partition
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hP:∀W∈P,∀Z∈P,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hspoke:∀v u,Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources ↔ H₀ v u∨Hₖ v u):
    ∃M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u),
      (∀u,(∀C∈M u,∀D∈M u,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D)) ∧
        (M u).biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u) ∧
        (M u).image (hubCycleWheel u)=P.filter (fun W=>W.2.val=u)) ∧
      (∀u v:U,u≠v→Disjoint ((M u).biUnion (hubCyclePhysicalEdges u)) ((M v).biUnion (hubCyclePhysicalEdges v))) ∧
      Finset.univ.biUnion (fun u=>(M u).biUnion (hubCyclePhysicalEdges u))=
        P.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1) := by
  have hexist:=marked_packing_to_hub_factors P hP hspoke
  let M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u):=fun u=>Classical.choose (hexist u)
  have hM:∀u,(∀C∈M u,∀D∈M u,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D)) ∧
        (M u).biUnion (hubMarkedCycleVertices u)=Finset.univ.filter (fun v=>H₀ v u∨Hₖ v u) ∧
        (M u).image (hubCycleWheel u)=P.filter (fun W=>W.2.val=u):=fun u=>Classical.choose_spec (hexist u)
  have hmem:∀u C,C∈M u→hubCycleWheel u C∈P:=by
    intro u C hC
    have hh:hubCycleWheel u C∈(M u).image (hubCycleWheel u):=Finset.mem_image.mpr ⟨C,hC,rfl⟩
    rw [(hM u).2.2] at hh
    exact (Finset.mem_filter.mp hh).1
  refine ⟨M,hM,?_,?_⟩
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨C,hC,heC⟩:=Finset.mem_biUnion.mp he
    obtain ⟨D,hD,heD⟩:=Finset.mem_biUnion.mp hf
    have hne:hubCycleWheel u C≠hubCycleWheel v D:=by
      intro h
      have hh:=congrArg (fun W=>W.2.val) h
      exact huv hh
    have hd:=hP (hubCycleWheel u C) (hmem u C hC) (hubCycleWheel v D) (hmem v D hD) hne
    apply Finset.disjoint_left.mp hd
      ((markedWheelPhysicalResources_rim _ e).2 heC)
    exact (markedWheelPhysicalResources_rim _ e).2 heD
  · ext e
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨u,C,hC,he⟩
      exact ⟨hubCycleWheel u C,hmem u C hC,he⟩
    · rintro ⟨W,hW,he⟩
      let u:=W.2.val
      have hf:W∈P.filter (fun Z=>Z.2.val=u):=Finset.mem_filter.mpr ⟨hW,rfl⟩
      rw [←(hM u).2.2] at hf
      obtain ⟨C,hC,hCW⟩:=Finset.mem_image.mp hf
      refine ⟨u,C,hC,?_⟩
      change e∈markedCyclePhysicalEdges tail head ktail khead m π b (hubCycleWheel u C).1
      rw [hCW]
      exact he
end Oberwolfach
