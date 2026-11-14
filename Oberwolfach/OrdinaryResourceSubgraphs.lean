module

public import Oberwolfach.OrdinaryHostDecompositions
public import Oberwolfach.ResourceTransformers
public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.TransformerOriginalEdgeIdentity

@[expose] public section

/-! Recover genuine extended subgraphs from physical resource sets.
Unordered rim edges and ordered V-U spokes remain separate throughout.
The conversion is exact and carries both transformer decompositions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 def ordinaryResourceRim (Q:SimpleGraph V) (K:Finset (Sym2 V⊕(V×U))):SimpleGraph V where
  Adj v w:=Q.Adj v w∧Sum.inl s(v,w)∈K
  symm:=⟨by intro v w h;exact ⟨h.1.symm,by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless:=⟨by intro v h;exact Q.irrefl h.1⟩

 theorem ordinary_resource_subgraph (Q:SimpleGraph V) (H:V→U→Prop)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H):
    ordinaryResourceRim Q K≤Q∧(∀ v u,Sum.inr (v,u)∈K→H v u)∧
      ordinaryHostResources (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)=K:=by
  refine ⟨fun _ _ h=>h.1,(fun v u h=>(ordinaryHostResources_spoke Q H v u).mp (hK h)),?_⟩
  ext e
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      rw [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet]
      change (Q.Adj v w∧Sum.inl s(v,w)∈K)↔Sum.inl s(v,w)∈K
      exact ⟨And.right,fun h=>⟨(ordinaryHostResources_rim Q H _).mp (hK h),h⟩⟩
  | inr vu=>
    rcases vu with ⟨v,u⟩
    exact ordinaryHostResources_spoke _ _ v u

 theorem transformer_image_resources_subhost (G Q:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (hQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hH:∀ v u,H₀ v u→H (φ v) (ψ u)):
    transformerImageResources G H₀ φ ψ⊆ordinaryHostResources Q H:=by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
    exact (ordinaryHostResources_rim Q H _).mpr (hQ _ _ (edge_out_adj G i))
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
    exact (ordinaryHostResources_spoke Q H _ _).mpr (hH _ _ i.property)

 theorem ordinary_transformer_graph_realization (Q F L L':SimpleGraph V)
    (H H₀ H₁:V→U→Prop) (r:ℕ) (K:Finset (Sym2 V⊕(V×U)))
    (hK:K⊆ordinaryHostResources Q H)
    (ht:IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources L H₀) (ordinaryHostResources L' H₁) K):
    let R:=ordinaryResourceRim Q K
    let S:V→U→Prop:=fun v u=>Sum.inr (v,u)∈K
    R≤Q∧(∀ v u,S v u→H v u)∧
    Disjoint R L∧Disjoint R L'∧
    (∀ v u,¬(S v u∧H₀ v u))∧(∀ v u,¬(S v u∧H₁ v u))∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (R⊔L) (fun v u=>S v u∨H₀ v u))∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (R⊔L') (fun v u=>S v u∨H₁ v u)):=by
  dsimp only
  have hs:=ordinary_resource_subgraph Q H K hK
  refine ⟨hs.1,hs.2.1,?_,?_,?_,?_,?_,?_⟩
  · apply disjoint_iff_inf_le.mpr
    intro v w hh
    exact (Finset.disjoint_left.mp ht.1 hh.1.2 ((ordinaryHostResources_rim L H₀ _).mpr hh.2)).elim
  · apply disjoint_iff_inf_le.mpr
    intro v w hh
    exact (Finset.disjoint_left.mp ht.2.1 hh.1.2 ((ordinaryHostResources_rim L' H₁ _).mpr hh.2)).elim
  · intro v u hh
    exact Finset.disjoint_left.mp ht.1 hh.1 ((ordinaryHostResources_spoke L H₀ v u).mpr hh.2)
  · intro v u hh
    exact Finset.disjoint_left.mp ht.2.1 hh.1 ((ordinaryHostResources_spoke L' H₁ v u).mpr hh.2)
  · rw [ordinaryHostResources_union,hs.2.2]
    exact ht.2.2.1
  · rw [ordinaryHostResources_union,hs.2.2]
    exact ht.2.2.2

 theorem ordinary_resource_subgraph_order (Q:SimpleGraph V) (H:V→U→Prop)
    (K:Finset (Sym2 V⊕(V×U))) (hK:K⊆ordinaryHostResources Q H)
    (N:Finset V) (B:Finset U)
    (hR:∀ v w,Sum.inl s(v,w)∈K→v∈N∧w∈N)
    (hS:∀ v u,Sum.inr (v,u)∈K→v∈N∧u∈B):
    (ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset.card≤N.card+B.card:=by
  have hsub:(ordinaryPhysicalGraph (ordinaryResourceRim Q K) (fun v u=>Sum.inr (v,u)∈K)).support.toFinset⊆
      N.image Sum.inl∪B.image Sum.inr:=by
    intro x hx
    obtain ⟨y,hy⟩:=Set.mem_toFinset.mp hx
    cases x with
    | inl v=>
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨v,?_,rfl⟩
      cases y with
      | inl w=>exact (hR v w hy.2).1
      | inr u=>exact (hS v u hy).1
    | inr u=>
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨u,?_,rfl⟩
      cases y with
      | inl v=>exact (hS v u hy).2
      | inr z=>exact hy.elim
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le))

end Oberwolfach
