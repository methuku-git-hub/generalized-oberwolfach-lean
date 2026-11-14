module

public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! Removing an ordinary rim/spoke subgraph changes each physical
    neighborhood by at most the degree of the removed physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_cleanup_edit
    (Q R:SimpleGraph V) (H S:V→U→Prop) (L:ℝ)
    (hdeg:∀w:V⊕U,((ordinaryPhysicalGraph R S).degree w:ℝ)≤L):
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\R) (fun v u=>H v u∧¬S v u)).neighborFinset w)).card:ℝ)≤L:=by
  intro w
  have hsub:changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\R) (fun v u=>H v u∧¬S v u)).neighborFinset w)⊆
        (ordinaryPhysicalGraph R S).neighborFinset w:=by
    intro z hz
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset] at hz ⊢
    cases w <;> cases z <;> simp only [ordinaryPhysicalGraph,SimpleGraph.sdiff_adj] at hz ⊢ <;> tauto
  have hc:((changed ((ordinaryPhysicalGraph Q H).neighborFinset w)
      ((ordinaryPhysicalGraph (Q\R) (fun v u=>H v u∧¬S v u)).neighborFinset w)).card:ℝ)≤
      (ordinaryPhysicalGraph R S).degree w:=by
    have hh:=Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
    exact_mod_cast hh
  exact hc.trans (hdeg w)
end Oberwolfach
