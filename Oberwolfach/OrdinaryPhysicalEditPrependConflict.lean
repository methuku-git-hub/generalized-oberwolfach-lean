module

public import Oberwolfach.OrdinaryProtectedCorrectionWithForbiddenEdit

@[expose] public section
/-! Add the conflict-deletion cost to a bound from the conflict-deleted
sample to any actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_edit_prepend_conflict
    (R F G:SimpleGraph V) (J H:V→U→Prop) (LF L:ℝ)
    (hLF:0≤LF) (hF:∀v,(F.degree v:ℝ)≤LF)
    (hbase:∀w:V⊕U,((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)
      ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤L):
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤LF+L :=by
  intro w
  have hfirst:=ordinary_physical_forbidden_rim_edit R F J LF hLF hF w
  have ht:((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R J).neighborFinset w) ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph G H).neighborFinset w)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph G H).neighborFinset w)
  linarith only [ht,hfirst,hbase w]
end Oberwolfach
