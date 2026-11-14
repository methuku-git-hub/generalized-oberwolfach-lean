module

public import Oberwolfach.WheelFamilyDeletionChanges
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! A realised wheel-family deletion consumes its actual rim and spoke
degrees from the running deviation budget at the next level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z:Type} [Fintype V] [Fintype U] [Fintype Z] [DecidableEq V] [DecidableEq U]

theorem ordinary_level_deletion_change_budget
    (Reference Q F:SimpleGraph V) (Href H:V→U→Prop) (r:ℕ)
    (C:Z→OrdinaryWheel Q F H r) (bR bRow bCol dR dRow dCol:ℝ)
    (hR:∀v,((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤bR)
    (hRow:∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)≤bRow)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤bCol)
    (hDR:∀v,((wheelFamilyRim C).degree v:ℝ)≤dR)
    (hDRow:∀v,((Finset.univ.filter (wheelFamilySpokes C v)).card:ℝ)≤dRow)
    (hDCol:∀u,((Finset.univ.filter (fun v=>wheelFamilySpokes C v u)).card:ℝ)≤dCol):
    (∀v,((changed (Reference.neighborFinset v) ((Q\wheelFamilyRim C).neighborFinset v)).card:ℝ)≤bR+dR) ∧
    (∀v,((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ)≤bRow+dRow) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ)≤bCol+dCol):=by
  constructor
  · intro v
    have hh:((changed (Reference.neighborFinset v) ((Q\wheelFamilyRim C).neighborFinset v)).card:ℝ)≤
        ((changed (Reference.neighborFinset v) (Q.neighborFinset v)).card:ℝ)+
        ((changed (Q.neighborFinset v) ((Q\wheelFamilyRim C).neighborFinset v)).card:ℝ):=by
      exact_mod_cast changed_card_triangle (Reference.neighborFinset v) (Q.neighborFinset v) ((Q\wheelFamilyRim C).neighborFinset v)
    rw [wheel_family_rim_deletion_change C v] at hh
    linarith [hR v,hDR v]
  constructor
  · intro v
    have hh:((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (fun u=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ)≤
        ((changed (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))).card:ℝ)+
        ((changed (Finset.univ.filter (H v)) (Finset.univ.filter (fun u=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ):=by
      exact_mod_cast changed_card_triangle (Finset.univ.filter (Href v)) (Finset.univ.filter (H v))
        (Finset.univ.filter (fun u=>H v u∧¬wheelFamilySpokes C v u))
    rw [wheel_family_spoke_row_deletion_change C v] at hh
    linarith [hRow v,hDRow v]
  · intro u
    have hh:((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ)≤
        ((changed (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)+
        ((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u))).card:ℝ):=by
      exact_mod_cast changed_card_triangle (Finset.univ.filter (fun v=>Href v u)) (Finset.univ.filter (fun v=>H v u))
        (Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u))
    rw [wheel_family_spoke_column_deletion_change C u] at hh
    linarith [hCol u,hDCol u]
end Oberwolfach
