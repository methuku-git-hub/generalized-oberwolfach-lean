module

public import Oberwolfach.OrdinaryPhysicalEditFromTypedChanges

@[expose] public section
/-! Restore the original reference graph at the explicit cost of its
forbidden-edge degree, while retaining the same physical spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forbidden_reference_physical_edit
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (R F Q:SimpleGraph V) (J H:V→U→Prop) (cost LF:ℝ) (hLF:0≤LF)
    (hF:∀v,(F.degree v:ℝ)≤LF)
    (hphysical:∀w:V⊕U,((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤cost):
    ∀w:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤cost+LF :=by
  have hr:∀v,((changed (R.neighborFinset v) ((R\F).neighborFinset v)).card:ℝ)≤LF:=by
    intro v
    have hsub:changed (R.neighborFinset v) ((R\F).neighborFinset v)⊆F.neighborFinset v:=by
      intro w hw
      simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj] at hw ⊢
      tauto
    have hh:=Finset.card_le_card hsub
    have hr':((changed (R.neighborFinset v) ((R\F).neighborFinset v)).card:ℝ)≤(F.degree v:ℝ):=by exact_mod_cast hh
    exact hr'.trans (hF v)
  have hreference:=ordinary_physical_edit_of_equal_spokes R (R\F) J LF hLF
    (by intro v;convert hr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  intro w
  have htri:((changed ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R J).neighborFinset w) ((ordinaryPhysicalGraph (R\F) J).neighborFinset w)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R J).neighborFinset w)
      ((ordinaryPhysicalGraph (R\F) J).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)
  linarith [hreference w,hphysical w]
end Oberwolfach
