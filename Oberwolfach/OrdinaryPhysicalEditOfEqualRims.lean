module

public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! If the rim graph is unchanged, physical edits are exactly the changes in
the corresponding spoke row or column. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_edit_of_equal_rims
    (Q:SimpleGraph V) (J H:V→U→Prop) (L:ℝ)
    (hrow:∀v,((changed (Finset.univ.filter (J v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>J v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L):
    ∀a:V⊕U,((changed ((ordinaryPhysicalGraph Q J).neighborFinset a)
      ((ordinaryPhysicalGraph Q H).neighborFinset a)).card:ℝ)≤L:=by
  intro a
  cases a with
  | inl v=>
    have he:changed ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inl v))
        ((ordinaryPhysicalGraph Q H).neighborFinset (Sum.inl v))=
        (changed (Finset.univ.filter (J v)) (Finset.univ.filter (H v))).image Sum.inr:=by
      ext b
      cases b <;> simp [changed,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [he,Finset.card_image_of_injective _ Sum.inr_injective]
    exact hrow v
  | inr u=>
    have he:changed ((ordinaryPhysicalGraph Q J).neighborFinset (Sum.inr u))
        ((ordinaryPhysicalGraph Q H).neighborFinset (Sum.inr u))=
        (changed (Finset.univ.filter (fun v=>J v u)) (Finset.univ.filter (fun v=>H v u))).image Sum.inl:=by
      ext b
      cases b <;> simp [changed,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [he,Finset.card_image_of_injective _ Sum.inl_injective]
    exact hcol u
end Oberwolfach
