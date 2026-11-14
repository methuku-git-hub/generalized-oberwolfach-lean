module

public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Global rim and spoke-row changes after a hub packing are charged to its
actual rim degrees and to the number of selected hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh:ℕ}

theorem ordinary_hub_deletion_global_rim_change
    (M:Finset (OrdinaryWheel Q F H r)) (u:Fin nh→U) (T:Fin nh→Finset V)
    (hMdeg:∀v,(ordinaryWheelRimGraph M).degree v≤2*nh)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i)))):
    ∀v,(changed (Q.neighborFinset v) ((Q\ordinaryWheelRimGraph M).neighborFinset v)).card≤2*nh:=by
  intro v
  have hh:=(ordinary_hub_deletion_fixed_domain M u T Finset.univ (∅:Finset U) (by simp) hunion hMdeg).1 v
  simpa only [Finset.univ_inter] using hh

theorem ordinary_hub_deletion_global_spoke_row_change
    (M:Finset (OrdinaryWheel Q F H r)) (u:Fin nh→U) (T:Fin nh→Finset V)
    (hunion:M.biUnion ordinaryWheelResources=(ordinaryWheelRimGraph M).edgeFinset.image Sum.inl ∪
      Finset.univ.biUnion (fun i=>(T i).image (fun v=>Sum.inr (v,u i)))):
    ∀v,(changed (Finset.univ.filter (H v))
      (Finset.univ.filter (fun a=>H v a∧¬ordinaryPackingSpokes M v a))).card≤nh:=by
  intro v
  have hsub:changed (Finset.univ.filter (H v))
      (Finset.univ.filter (fun a=>H v a∧¬ordinaryPackingSpokes M v a))⊆
      Finset.univ.filter (ordinaryPackingSpokes M v):=by
    intro a ha
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
    tauto
  exact (Finset.card_le_card hsub).trans (ordinary_hub_packing_row_degree M u T hunion v)
end Oberwolfach
