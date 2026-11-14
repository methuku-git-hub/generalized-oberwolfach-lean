module

public import Oberwolfach.MarkedRowCoverRestrictionLift
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! A packing constructed in the host after deleting a physical graph
avoids that graph on both its rim and spoke edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_restricted_packing_physical_avoidance (D:SimpleGraph (V⊕U))
    (M:Finset (MarkedWheel
      (fun e:{e:E // ¬D.Adj (Sum.inl (tail e)) (Sum.inl (head e))}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
        (fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)))):
    Disjoint (ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)) D:=by
  have hr (x y:V) (hxy:(markedPackingRimGraph M).Adj x y):¬D.Adj (Sum.inl x) (Sum.inl y):=by
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hxy.2
    exact marked_cycle_rim_avoids_deleted_graph (D.comap (Sum.inl:V→V⊕U)) W.1 x y he
  have hs (x:V) (u:U) (hxu:markedPackingSpokes M x u):¬D.Adj (Sum.inl x) (Sum.inr u):=by
    obtain ⟨W,hW,hu,hx⟩:=hxu
    have hh:=markedWheelPhysicalResources_spoke_present W x u
      ((markedWheelPhysicalResources_spoke W x u).mpr ⟨hu,hx⟩)
    exact hh.elim (fun h=>h.2) (fun h=>h.2)
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  cases x with
  | inl x=>cases y with
    | inl y=>exact (hr x y hxy.1 hxy.2).elim
    | inr y=>exact (hs x y hxy.1 hxy.2).elim
  | inr x=>cases y with
    | inl y=>exact (hs y x hxy.1 ((D.adj_comm _ _).mp hxy.2)).elim
    | inr y=>exact hxy.1

end Oberwolfach
