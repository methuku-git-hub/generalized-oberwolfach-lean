module

public import Oberwolfach.PhysicalHostDegreeBounds
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! Upper degree estimates for the actual sample and a single physical edit
bound give the degree cap required by general boundary wheel completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_degree_from_sample_edit
    (Qraw Q:SimpleGraph V) (Hraw H:V→U→Prop) (r s c L:ℝ)
    (hr:∀v,(Qraw.degree v:ℝ)≤r)
    (hs:∀v,((Finset.univ.filter (Hraw v)).card:ℝ)≤s)
    (hc:∀u,((Finset.univ.filter (fun v=>Hraw v u)).card:ℝ)≤c)
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph Qraw Hraw).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L):
    ∀w:V⊕U,((ordinaryPhysicalGraph Q H).degree w:ℝ)≤max (r+s) c+L:=by
  have hraw:=ordinary_physical_degree_bound Qraw Hraw r s c (max (r+s) c) hr hs hc
    (le_max_left _ _) (le_max_right _ _)
  intro w
  have hchange:=card_difference_le_changed ((ordinaryPhysicalGraph Qraw Hraw).neighborFinset w)
    ((ordinaryPhysicalGraph Q H).neighborFinset w)
  rw [SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.card_neighborFinset_eq_degree] at hchange
  have hh:=(abs_le.mp hchange).1
  linarith only [hh,hedit w,hraw w]

theorem ordinary_physical_degree_cap_from_sample_edit
    (Qraw Q:SimpleGraph V) (Hraw H:V→U→Prop) (r s c L:ℝ)
    (hr:∀v,(Qraw.degree v:ℝ)≤r)
    (hs:∀v,((Finset.univ.filter (Hraw v)).card:ℝ)≤s)
    (hc:∀u,((Finset.univ.filter (fun v=>Hraw v u)).card:ℝ)≤c)
    (hedit:∀w:V⊕U,((changed ((ordinaryPhysicalGraph Qraw Hraw).neighborFinset w)
      ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L) (hb:0≤max (r+s) c+L):
    ∃D:ℕ,(∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤D) ∧
      (D:ℝ)≤max (r+s) c+L+1:=by
  have hbound:=ordinary_physical_degree_from_sample_edit Qraw Q Hraw H r s c L hr hs hc hedit
  let b:=max (r+s) c+L
  refine ⟨⌈b⌉₊,?_,(Nat.ceil_lt_add_one hb).le⟩
  intro w
  exact_mod_cast (hbound w).trans (Nat.le_ceil b)
end Oberwolfach
