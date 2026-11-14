module

public import Oberwolfach.OrdinaryRootCoverNonrootEditBounds
public import Oberwolfach.OrdinaryChangedSubtypeBound
public import Oberwolfach.OrdinaryInducedRimCutEdits

@[expose] public section
/-! After a small-load root cover, the exact restricted rim and spoke
profiles remain close to the original sample on the nonroot domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_restricted_edits
    (Reference Q F:SimpleGraph V) (Href H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (r:ℕ) (η ell L:ℝ) (A:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (hR:∀v∉T,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hRow:∀v∉T,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hCol:∀u∉W,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    (∀v:Vfree,((changed ((Reference.induce (Vfree:Set V)).neighborFinset v)
      ((Q'.induce (Vfree:Set V)).neighborFinset v)).card:ℝ)≤L+ell) ∧
    (∀v:Vfree,((changed (Finset.univ.filter (fun u:Ufree=>Href v.val u.val))
      (Finset.univ.filter (fun u:Ufree=>H' v.val u.val))).card:ℝ)≤L+ell) ∧
    (∀u:Ufree,((changed (Finset.univ.filter (fun v:Vfree=>Href v.val u.val))
      (Finset.univ.filter (fun v:Vfree=>H' v.val u.val))).card:ℝ)≤L+ell):=by
  intro Vfree Ufree Q' H'
  have he:=ordinary_root_cover_nonroot_edit_bounds Reference Q F Href H X T Z W r η ell L A hR hRow hCol
  refine ⟨?_,?_,?_⟩
  · intro v
    have hv:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
    have hh:=ordinary_induced_changed_rim_bound_general Reference Q' Vfree v
    apply le_trans ?_ (he.1 v.val hv)
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro v
    have hv:v.val∉T:=(Finset.mem_sdiff.mp v.property).2
    have hh:=ordinary_changed_subtype_bound Ufree (Href v.val) (H' v.val)
    apply le_trans ?_ (he.2.1 v.val hv)
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro u
    have hu:u.val∉W:=(Finset.mem_sdiff.mp u.property).2
    have hh:=ordinary_changed_subtype_bound Vfree (fun v=>Href v u.val) (fun v=>H' v u.val)
    apply le_trans ?_ (he.2.2 u.val hu)
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
