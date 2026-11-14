module

public import Oberwolfach.OrdinaryDeepRootFreeFamilies

@[expose] public section
/-! Avoiding the entire physical star of a deep pair makes its boundary
empty, a strictly stronger conclusion than a global degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edge_touching_deep_root_star (Q:SimpleGraph V) (H:V→U→Prop)
    (T:Finset V) (W:Finset U) (a b:V⊕U) (hab:(ordinaryPhysicalGraph Q H).Adj a b)
    (hroot:a∈ordinaryInnerVertices T W∨b∈ordinaryInnerVertices T W):
    (ordinaryDeepRootStar T W).Adj a b:=by
  cases a with
  | inl v=>cases b with
    | inl w=>
      have h:(v∈T∨w∈T):=by simpa only [ordinaryInnerVertices_left] using hroot
      exact ⟨by intro he;subst w;exact hab.ne rfl,h⟩
    | inr u=>
      have h:(v∈T∨u∈W):=by simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hroot
      exact ⟨trivial,h⟩
  | inr u=>cases b with
    | inl v=>
      have h:(v∈T∨u∈W):=by
        have hh:(u∈W∨v∈T):=by simpa only [ordinaryInnerVertices_left,ordinaryInnerVertices_right] using hroot
        exact hh.symm
      exact ⟨trivial,h⟩
    | inr z=>exact hab.elim

theorem ordinary_root_star_avoided_boundary_empty (Q:SimpleGraph V) (H:V→U→Prop)
    (T:Finset V) (W:Finset U)
    (havoid:Disjoint (ordinaryPhysicalGraph Q H) (ordinaryDeepRootStar T W)):
    ordinaryBoundaryGraph Q H T W=⊥:=by
  apply le_antisymm
  · intro a b hab
    have hh:=(ordinaryBoundaryGraph_adj Q H T W a b).mp hab
    have hroot:a∈ordinaryInnerVertices T W∨b∈ordinaryInnerVertices T W:=by
      rcases hh.2 with h|h
      · exact Or.inr h.2
      · exact Or.inl h.2
    exact (disjoint_iff_inf_le.mp havoid) ⟨hh.1,ordinary_edge_touching_deep_root_star Q H T W a b hh.1 hroot⟩
  · exact bot_le
end Oberwolfach
