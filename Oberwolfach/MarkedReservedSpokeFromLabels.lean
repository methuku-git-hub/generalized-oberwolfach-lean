module

public import Oberwolfach.MarkedFixedReservoirFromChangeGraph

@[expose] public section
/-! The precise label exclusions which preserve reserved marked and
ordinary spokes in the residual host of the long preparation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_reserved_spokes_from_label_exclusions
    (C:Finset (Finset V⊕(V×U))) (Hold:Bool→V→U→Prop)
    (Y Z B:U→Finset V) (Hnew:Bool→V→U→Prop)
    (hmarked:∀ v u,Hnew true v u↔v∈Y u)
    (hordinary:∀ v u,Hnew false v u↔v∉Z u∧v∉B u∧v∉Y u)
    (hfixed:∀ v u,Sum.inr (v,u)∈C→Hold true v u→v∈Y u)
    (hdisjoint:∀ v u,Hold false v u→v∉Y u)
    (havoid:∀ v u,Sum.inr (v,u)∈C→Hold false v u→v∉Z u∧v∉B u):
    ∀ b v u,Sum.inr (v,u)∈C→Hold b v u→Hnew b v u :=by
  intro b v u he hh
  cases b
  · exact (hordinary v u).mpr ⟨(havoid v u he hh).1,(havoid v u he hh).2,hdisjoint v u hh⟩
  · exact (hmarked v u).mpr (hfixed v u he hh)
end Oberwolfach
