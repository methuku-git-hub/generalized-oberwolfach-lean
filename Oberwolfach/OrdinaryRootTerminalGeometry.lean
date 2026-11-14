module

public import Oberwolfach.OrdinaryRootResources
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! Root containment controls the terminal graph's order and permits local
host and spoke containment to be checked only on the terminal pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_terminal_root_geometry (G:SimpleGraph V) (H:V→U→Prop)
    (W:Finset V) (B:Finset U)
    (hroot:ordinaryHostResources G H⊆ordinaryRootResources W B):
    (ordinaryPhysicalGraph G H).support.toFinset.card≤W.card+B.card ∧
    (∀v w,G.Adj v w→v∈W∧w∈W) ∧ (∀v u,H v u→v∈W∧u∈B):=by
  have hr:∀v w,G.Adj v w→v∈W∧w∈W:=by
    intro v w h
    exact (ordinaryRootResources_rim_iff W B v w).mp
      (hroot ((ordinaryHostResources_rim G H s(v,w)).mpr h))
  have hs:∀v u,H v u→v∈W∧u∈B:=by
    intro v u h
    exact (ordinaryRootResources_spoke_iff W B v u).mp
      (hroot ((ordinaryHostResources_spoke G H v u).mpr h))
  have hsub:(ordinaryPhysicalGraph G H).support.toFinset⊆
      W.image Sum.inl∪B.image Sum.inr:=by
    intro x hx
    obtain ⟨y,hy⟩:=Set.mem_toFinset.mp hx
    cases x with
    | inl v=>
      apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨v,?_,rfl⟩
      cases y with
      | inl w=>exact (hr v w hy).1
      | inr u=>exact (hs v u hy).1
    | inr u=>
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨u,?_,rfl⟩
      cases y with
      | inl v=>exact (hs v u hy).2
      | inr z=>exact hy.elim
  exact ⟨(Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)),hr,hs⟩

theorem ordinary_terminal_root_local_host (G P:SimpleGraph V) (H Hbase:V→U→Prop)
    (W:Finset V) (B:Finset U)
    (hroot:ordinaryHostResources G H⊆ordinaryRootResources W B)
    (hP:∀v∈W,∀w∈W,G.Adj v w→P.Adj v w)
    (hH:∀v∈W,∀u∈B,H v u→Hbase v u):
    G≤P ∧ (∀v u,H v u→Hbase v u):=by
  obtain ⟨_,hr,hs⟩:=ordinary_terminal_root_geometry G H W B hroot
  constructor
  · intro v w hvw
    exact hP v (hr v w hvw).1 w (hr v w hvw).2 hvw
  · intro v u hvu
    exact hH v (hs v u hvu).1 u (hs v u hvu).2 hvu
end Oberwolfach
