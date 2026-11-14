module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Inside the enclosing pair, the second deep-cover packing avoids all
nonroot vertices and hubs, so its union has exactly the first packing's
physical degree there. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_deep_union_nonroot_degree
    (PE:Finset (OrdinaryWheel Q F H r))
    (M:Finset (OrdinaryWheel (Q\ordinaryWheelRimGraph PE) F (fun v u=>H v u∧¬ordinaryPackingSpokes PE v u) r))
    (R:Finset (OrdinaryWheel Q F H r)) (I T:Finset V) (J W:Finset U)
    (hRrim:ordinaryWheelRimGraph R=ordinaryWheelRimGraph PE⊔ordinaryWheelRimGraph M)
    (hRsp:∀v u,ordinaryPackingSpokes R v u↔ordinaryPackingSpokes PE v u∨ordinaryPackingSpokes M v u)
    (hMavoidR:∀v∈I\T,∀w,¬(ordinaryWheelRimGraph M).Adj v w)
    (hMavoidS:∀v∈I\T,∀u,¬ordinaryPackingSpokes M v u)
    (hMavoidC:∀u∈J\W,∀v,¬ordinaryPackingSpokes M v u):
    (∀v∈I\T,(ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v)=
      (ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree (Sum.inl v)) ∧
    (∀u∈J\W,(ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u)=
      (ordinaryPhysicalGraph (ordinaryWheelRimGraph PE) (ordinaryPackingSpokes PE)).degree (Sum.inr u)):=by
  constructor
  · intro v hv
    have hneigh:(ordinaryWheelRimGraph R).neighborFinset v=(ordinaryWheelRimGraph PE).neighborFinset v:=by
      ext w
      simp only [SimpleGraph.mem_neighborFinset,hRrim,SimpleGraph.sup_adj]
      exact or_iff_left (hMavoidR v hv w)
    have hdeg:(ordinaryWheelRimGraph R).degree v=(ordinaryWheelRimGraph PE).degree v:=by
      have h:=congrArg Finset.card hneigh
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using h
    have hrow:Finset.univ.filter (ordinaryPackingSpokes R v)=Finset.univ.filter (ordinaryPackingSpokes PE v):=by
      ext u
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hRsp]
      exact or_iff_left (hMavoidS v hv u)
    rw [ordinary_physical_degree_row,ordinary_physical_degree_row,hdeg,hrow]
  · intro u hu
    have hcol:Finset.univ.filter (fun v=>ordinaryPackingSpokes R v u)=
        Finset.univ.filter (fun v=>ordinaryPackingSpokes PE v u):=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,hRsp]
      exact or_iff_left (hMavoidC u hu v)
    rw [ordinary_physical_degree_column,ordinary_physical_degree_column,hcol]
end Oberwolfach
