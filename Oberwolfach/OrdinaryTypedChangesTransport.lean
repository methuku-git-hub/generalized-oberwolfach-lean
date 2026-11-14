module

public import Oberwolfach.OrdinaryTypedChangesRestrict

@[expose] public section
/-! Replacing graph and spoke descriptions by equal ones preserves the
three edit bounds, including their dependent finite-set instances. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_typed_changes_transport
    (P Q P' Q':SimpleGraph V) (H J H' J':V→U→Prop) (L:ℝ)
    (hP:P=P') (hQ:Q=Q') (hH:H=H') (hJ:J=J')
    (h:(∀v,((changed (P.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) ∧
       (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) ∧
       (∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L)):
    (∀v,((changed (P'.neighborFinset v) (Q'.neighborFinset v)).card:ℝ)≤L) ∧
    (∀v,((changed (Finset.univ.filter (H' v)) (Finset.univ.filter (J' v))).card:ℝ)≤L) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>H' v u)) (Finset.univ.filter (fun v=>J' v u))).card:ℝ)≤L) :=by
  subst P'
  subst Q'
  subst H'
  subst J'
  exact h
end Oberwolfach
