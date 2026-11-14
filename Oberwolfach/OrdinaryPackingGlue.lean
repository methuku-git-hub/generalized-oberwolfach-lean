module

public import Oberwolfach.HubToRowDeletion
public import Oberwolfach.OrdinaryPackingTransport

@[expose] public section

/-! Glue a physical wheel packing to a second packing constructed in its
actual remainder. Lifting retains every rim edge and spoke exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_wheel_packing_glue_with_origins (M:Finset (OrdinaryWheel Q F H r))
    (N:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v u=>H v u∧¬ordinaryPackingSpokes M v u) r))
    (hM:∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (hN:∀ A∈N,∀ B∈N,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)):
    ∃ P:Finset (OrdinaryWheel Q F H r),
      (∀ A∈P,∀ B∈P,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      P.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources∪N.biUnion ordinaryWheelResources ∧
      ordinaryWheelRimGraph P=ordinaryWheelRimGraph M⊔ordinaryWheelRimGraph N ∧
      (∀ v u,ordinaryPackingSpokes P v u↔ordinaryPackingSpokes M v u∨ordinaryPackingSpokes N v u) ∧
      (∀ W∈P,W∈M∨∃ Z∈N,ordinaryWheelRim W=ordinaryWheelRim Z ∧ ordinaryWheelHub W=ordinaryWheelHub Z):=by
  have hsp:∀ v u,(H v u∧¬ordinaryPackingSpokes M v u)→H v u:=fun _ _ h=>h.1
  let f:=ordinaryWheelToLarger (F:=F) (r:=r) (sdiff_le:Q\ordinaryWheelRimGraph M≤Q)
    hsp
  let N':=N.image f
  have ht:=ordinary_packing_transport (sdiff_le:Q\ordinaryWheelRimGraph M≤Q) hsp N hN
  have hN':∀ A∈N',∀ B∈N',A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B):=ht.1
  have hres:N'.biUnion ordinaryWheelResources=N.biUnion ordinaryWheelResources:=ht.2
  have hcross:Disjoint (N'.biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources):=by
    rw [hres]
    apply Finset.disjoint_left.mpr
    intro e he heM
    obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (ordinary_wheel_avoids_removed_packing M W) heW heM
  refine ⟨M∪N',?_,?_,?_,?_,?_⟩
  · intro A hA B hB hne
    rcases Finset.mem_union.mp hA with ha|ha <;> rcases Finset.mem_union.mp hB with hb|hb
    · exact hM A ha B hb hne
    · exact hcross.symm.mono (resource_subset_union _ M A ha) (resource_subset_union _ N' B hb)
    · exact hcross.mono (resource_subset_union _ N' A ha) (resource_subset_union _ M B hb)
    · exact hN' A ha B hb hne
  · rw [Finset.union_biUnion,hres]
  · ext v w
    have hr (S:Finset (OrdinaryWheel Q F H r)):
        (ordinaryWheelRimGraph S).Adj v w↔Sum.inl s(v,w)∈S.biUnion ordinaryWheelResources:=by
      simp only [Finset.mem_biUnion,ordinaryWheelResources_rim]
      exact ordinaryWheelRimGraph_edges S s(v,w)
    have hn:(ordinaryWheelRimGraph N).Adj v w↔Sum.inl s(v,w)∈N.biUnion ordinaryWheelResources:=by
      simp only [Finset.mem_biUnion,ordinaryWheelResources_rim]
      exact ordinaryWheelRimGraph_edges N s(v,w)
    rw [SimpleGraph.sup_adj,hr,hr,hn,Finset.union_biUnion,hres,Finset.mem_union]
  · intro v u
    rw [ordinaryPackingSpokes_iff,ordinaryPackingSpokes_iff,ordinaryPackingSpokes_iff,
      Finset.union_biUnion,hres,Finset.mem_union]

  · intro W hW
    rcases Finset.mem_union.mp hW with hW|hW
    · exact Or.inl hW
    · obtain ⟨Z,hZ,rfl⟩:=Finset.mem_image.mp hW
      exact Or.inr ⟨Z,hZ,rfl,rfl⟩

theorem ordinary_wheel_packing_glue (M:Finset (OrdinaryWheel Q F H r))
    (N:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph M) F
      (fun v u=>H v u∧¬ordinaryPackingSpokes M v u) r))
    (hM:∀ A∈M,∀ B∈M,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B))
    (hN:∀ A∈N,∀ B∈N,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)):
    ∃ P:Finset (OrdinaryWheel Q F H r),
      (∀ A∈P,∀ B∈P,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      P.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources∪N.biUnion ordinaryWheelResources ∧
      ordinaryWheelRimGraph P=ordinaryWheelRimGraph M⊔ordinaryWheelRimGraph N ∧
      (∀ v u,ordinaryPackingSpokes P v u↔ordinaryPackingSpokes M v u∨ordinaryPackingSpokes N v u):=by
  obtain ⟨P,hP,hres,hrim,hsp,_⟩:=ordinary_wheel_packing_glue_with_origins M N hM hN
  exact ⟨P,hP,hres,hrim,hsp⟩

end Oberwolfach
