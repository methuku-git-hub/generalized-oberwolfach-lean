module

public import Oberwolfach.MarkedPackingStarDeletionBounds

@[expose] public section

/-! In the remaining inner domains the deep packing contributes no
physical deletion at any ambient root. Only the prescribed packing is
charged, with its actual degree rather than a sampling-density multiple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_union_neighbour_inter_of_avoids {V:Type} [Fintype V] [DecidableEq V]
    (G H:SimpleGraph V) (A:Finset V) (hH:∀ x,∀ y∈A,¬H.Adj x y) (x:V):
    (G⊔H).neighborFinset x∩A=G.neighborFinset x∩A:=by
  ext y
  simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,SimpleGraph.sup_adj]
  constructor
  · rintro ⟨hG|hH',hy⟩
    · exact ⟨hG,hy⟩
    · exact (hH x y hy hH').elim
  · rintro ⟨hG,hy⟩;exact ⟨Or.inl hG,hy⟩

theorem graph_union_degree_of_no_neighbours {V:Type} [Fintype V] [DecidableEq V]
    (G H:SimpleGraph V) (x:V) (hH:∀ y,¬H.Adj x y):(G⊔H).degree x=G.degree x:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.sup_adj,hH,or_false]

variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem markedFiniteSpokeGraph_packing_adj
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (x:V) (u:U):
    (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj (Sum.inl x) (Sum.inr u)↔
      markedPackingSpokes M x u:=by
  rw [markedFiniteSpokeGraph_adj]
  simp only [Finset.mem_biUnion,markedWheelSpokePairs,Finset.mem_image,Finset.mem_univ,true_and,
    Prod.mk.injEq,markedPackingSpokes,markedWheelRows]
  aesop

theorem marked_deep_spoke_graph_avoids_inner
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (A:Finset V) (B:Finset U)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅):
    (∀ z,∀ x∈A,¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj z (Sum.inl x)) ∧
    (∀ z,∀ u∈B,¬(markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)).Adj z (Sum.inr u)):=by
  have hs:=marked_packing_star_avoidance_neighbours M A B hstar
  constructor
  · intro z x hx hadj
    cases z with
    | inl y=>exact (markedFiniteSpokeGraph_same_part _).1 y x hadj
    | inr u=>exact hs.2.2.2.1 x hx u ((markedFiniteSpokeGraph_packing_adj M x u).mp hadj.symm)
  · intro z u hu hadj
    cases z with
    | inr v=>exact (markedFiniteSpokeGraph_same_part _).2 v u hadj
    | inl x=>exact hs.2.2.2.2 u hu x ((markedFiniteSpokeGraph_packing_adj M x u).mp hadj)

theorem marked_inner_deletion_has_only_prescribed_cost
    (MD:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (A:Finset V) (B:Finset U)
    (hstar:(MD.biUnion markedWheelPhysicalResources).filter (markedStarResource A B)=∅)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U)):
    let DR:=ER⊔markedPackingRimGraph MD
    let DS:=ES⊔markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)
    (∀ x,DR.neighborFinset x∩A=ER.neighborFinset x∩A) ∧
    (∀ z,DS.neighborFinset z∩A.image Sum.inl=ES.neighborFinset z∩A.image Sum.inl) ∧
    (∀ z,DS.neighborFinset z∩B.image Sum.inr=ES.neighborFinset z∩B.image Sum.inr) ∧
    (∀ x∈A,DS.degree (Sum.inl x)=ES.degree (Sum.inl x)) ∧
    (∀ u∈B,DS.degree (Sum.inr u)=ES.degree (Sum.inr u)):=by
  have hr:∀ x,∀ y∈A,¬(markedPackingRimGraph MD).Adj x y:=by
    intro x y hy hadj
    have hm:y∈(markedPackingRimGraph MD).neighborFinset x∩A:=
      Finset.mem_inter.mpr ⟨((markedPackingRimGraph MD).mem_neighborFinset x y).mpr hadj,hy⟩
    rw [(marked_packing_star_avoidance_neighbours MD A B hstar).1 x] at hm
    exact Finset.notMem_empty y hm
  have hs:=marked_deep_spoke_graph_avoids_inner MD A B hstar
  dsimp only
  refine ⟨graph_union_neighbour_inter_of_avoids ER _ A hr,?_,?_,?_,?_⟩
  · apply graph_union_neighbour_inter_of_avoids
    intro z y hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    exact hs.1 z x hx
  · apply graph_union_neighbour_inter_of_avoids
    intro z y hy
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hy
    exact hs.2 z u hu
  · intro x hx
    apply graph_union_degree_of_no_neighbours
    intro z hz
    exact hs.1 z x hx hz.symm
  · intro u hu
    apply graph_union_degree_of_no_neighbours
    intro z hz
    exact hs.2 z u hu hz.symm

end Oberwolfach
