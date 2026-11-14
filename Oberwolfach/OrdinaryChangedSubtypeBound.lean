module

public import Oberwolfach.BoundarySupportChanges

@[expose] public section
/-! Restricting a finite relation to a subtype cannot increase the number of
changed elements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A:Type} [Fintype A] [DecidableEq A]

theorem ordinary_changed_subtype_bound (S:Finset A) (p q:A→Prop):
    ((changed (Finset.univ.filter (fun x:S=>p x.val))
      (Finset.univ.filter (fun x:S=>q x.val))).card:ℝ)≤
      ((changed (Finset.univ.filter p) (Finset.univ.filter q)).card:ℝ):=by
  let D:=changed (Finset.univ.filter (fun x:S=>p x.val)) (Finset.univ.filter (fun x:S=>q x.val))
  let E:=changed (Finset.univ.filter p) (Finset.univ.filter q)
  have hsub:D.image (Subtype.val:S→A)⊆E:=by
    intro a ha
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp ha
    simp only [D,E,changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] at hx ⊢
    exact hx
  have hcard:=Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
  exact_mod_cast hcard

theorem ordinary_induced_changed_rim_bound_general (Qraw Q:SimpleGraph A) (S:Finset A) (v:S):
    ((changed ((Qraw.induce (S:Set A)).neighborFinset v) ((Q.induce (S:Set A)).neighborFinset v)).card:ℝ)≤
      ((changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)).card:ℝ):=by
  have h:(changed ((Qraw.induce (S:Set A)).neighborFinset v) ((Q.induce (S:Set A)).neighborFinset v)).card≤
      (changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)).card:=by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro w hw
      change w ∈ changed ((Qraw.induce (S:Set A)).neighborFinset v) ((Q.induce (S:Set A)).neighborFinset v) at hw
      change w.val ∈ changed (Qraw.neighborFinset v.val) (Q.neighborFinset v.val)
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj] at hw ⊢
      exact hw
    · intro a _ b _ hab;exact Subtype.val_injective hab
  exact_mod_cast h
end Oberwolfach
