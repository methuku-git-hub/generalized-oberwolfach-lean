module

public import Oberwolfach.MarkedHubFactorOn
public import Oberwolfach.MarkedHubFactorLift

@[expose] public section

/-! Turn a factor on a selected subset of the parent neighbourhood into
actual wheels, covering exactly the selected spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem marked_selected_hub_factor_to_wheels (u:U) (hm:1≤m) (hb:1≤b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hsep:∀ v z,H₀ v u→Hₖ z u→v≠π z)
    (Y:Finset V) (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀ C∈M,∀ Z∈M,C≠Z→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u Z))
    (hcov:M.biUnion (hubMarkedCycleVertices u)=Y):
    ∃ N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      N.biUnion markedWheelPhysicalResources=(markedPackingRims N).image Sum.inl∪
        (Y).image (fun v=>Sum.inr (v,u))∧
      (∀ v,(markedPackingRimGraph N).degree v≤2)∧
      (∀ W∈N,W.2.val=u)∧(∀ e∈markedPackingRims N,e.card=2)∧
      markedPackingRims N=M.biUnion (hubCyclePhysicalEdges u):=by
  let N:=M.image (hubCycleWheel u)
  have hr:markedPackingRims N=M.biUnion (hubCyclePhysicalEdges u):=by
    rw [markedPackingRims,Finset.image_biUnion]
    rfl
  refine ⟨N,?_,?_,?_,?_,?_,hr⟩
  · intro W hW Z hZ hne
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨D,hD,rfl⟩:=Finset.mem_image.mp hZ
    have hCD:C≠D:=fun h=>hne (congrArg (hubCycleWheel u) h)
    apply Finset.disjoint_left.mpr
    intro e he hf
    cases e with
    | inl e=>
      rw [markedWheelPhysicalResources_rim] at he hf
      exact Finset.disjoint_left.mp (marked_factor_physical_edges_disjoint u hp M hM C hC D hD hCD) he hf
    | inr e=>
      rw [markedWheelPhysicalResources_spoke] at he hf
      exact Finset.disjoint_left.mp (hM C hC D hD hCD) he.2 hf.2
  · rw [←hcov]
    ext e
    cases e with
    | inl e=>
      simp only [Finset.mem_biUnion,markedWheelPhysicalResources_rim,Finset.mem_union,
        Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,
        exists_eq_right,markedPackingRims]
    | inr e=>
      rcases e with ⟨v,z⟩
      simp only [N,Finset.mem_biUnion,Finset.mem_image,markedWheelPhysicalResources_spoke,
        Finset.mem_union,Sum.inl_ne_inr,and_false,exists_false,false_or,Sum.inr.injEq,Prod.mk.injEq]
      constructor
      · rintro ⟨W,⟨C,hC,rfl⟩,he,hv⟩
        exact ⟨v,⟨C,hC,Finset.mem_image.mpr hv⟩,rfl,he⟩
      · rintro ⟨v,⟨C,hC,hv⟩,he,hu⟩
        exact ⟨hubCycleWheel u C,⟨C,hC,rfl⟩,hu,he ▸ (Finset.mem_image.mp hv)⟩
  · intro v
    change (physicalEdgeGraph (markedPackingRims N)).degree v≤2
    rw [hr]
    exact marked_factor_physical_degree u hsep M hM v
  · intro W hW
    obtain ⟨C,hC,rfl⟩:=Finset.mem_image.mp hW
    rfl
  · intro e he
    rw [hr] at he
    obtain ⟨C,hC,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i,hi,he⟩:=Finset.mem_image.mp he
    rw [←he]
    exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb (hubCycleAsMarked u C) i

end Oberwolfach
