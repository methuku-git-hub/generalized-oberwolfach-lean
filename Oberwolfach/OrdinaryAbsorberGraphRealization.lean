module

public import Oberwolfach.OrdinaryRelativeAmbientAbsorber

@[expose] public section

/-! Recover a genuine extended absorber graph and its two wheel
decompositions from the proved finite physical-resource construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_absorber_graph_realization (Q F G:SimpleGraph V) (H Hs:V→U→Prop)
    (r:ℕ) (C:Finset (Sym2 V⊕(V×U))) (hC:C⊆ordinaryHostResources Q H)
    (habs:IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources G Hs) C) (a b:ℕ)
    (hrows:(ordinaryResourceRows C).card≤a) (hhubs:(ordinaryResourceHubs C).card≤b)
    (W:Finset V) (B:Finset U) (havoid:Disjoint C (ordinaryRootResources W B)) :
    let R:=ordinaryResourceRim Q C
    let K:V→U→Prop:=fun v u=>Sum.inr (v,u)∈C
    R≤Q∧(∀ v u,K v u→H v u)∧Disjoint R G∧(∀ v u,¬(K v u∧Hs v u))∧
    (ordinaryPhysicalGraph R K).support.toFinset.card≤a+b∧
    (∀ v∈W,∀ w∈W,¬R.Adj v w)∧(∀ v∈W,∀ u∈B,¬K v u)∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R K)∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (R⊔G) (fun v u=>K v u∨Hs v u)) := by
  dsimp only
  have hs:=ordinary_resource_subgraph Q H C hC
  have hr:∀ v w,Sum.inl s(v,w)∈C→v∈ordinaryResourceRows C∧w∈ordinaryResourceRows C:=by
    intro v w h
    exact ⟨Finset.mem_biUnion.mpr ⟨_,h,by simp⟩,Finset.mem_biUnion.mpr ⟨_,h,by simp⟩⟩
  have hh:∀ v u,Sum.inr (v,u)∈C→v∈ordinaryResourceRows C∧u∈ordinaryResourceHubs C:=by
    intro v u h
    exact ⟨Finset.mem_biUnion.mpr ⟨_,h,by simp⟩,Finset.mem_biUnion.mpr ⟨_,h,by simp⟩⟩
  have horder:=(ordinary_resource_subgraph_order Q H C hC _ _ hr hh).trans (Nat.add_le_add hrows hhubs)
  have hroot:=ordinaryRootResources_avoid C W B havoid
  refine ⟨hs.1,hs.2.1,?_,?_,horder,?_,hroot.2,?_,?_⟩
  · apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (Finset.disjoint_left.mp habs.1 h.1.2 ((ordinaryHostResources_rim _ _ _).mpr h.2)).elim
  · intro v u h
    exact Finset.disjoint_left.mp habs.1 h.1 ((ordinaryHostResources_spoke _ _ _ _).mpr h.2)
  · intro v hv w hw h
    exact hroot.1 v hv w hw h.2
  · rw [hs.2.2];exact habs.2.1
  · rw [ordinaryHostResources_union,hs.2.2];exact habs.2.2

end Oberwolfach
