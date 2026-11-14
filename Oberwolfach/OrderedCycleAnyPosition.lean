module

public import Oberwolfach.OrderedCycleReparametrisation
public import Oberwolfach.OrderedCycleFirstVertexCount

@[expose] public section
/-! At any prescribed position, the corresponding directed edge determines
the ordered representation, and each vertex occurs in its degree many. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleNext_eq_add_one (n:ℕ) (i:Fin (n+2)):cycleNext i=i+1:=by
  apply Fin.ext
  simp [cycleNext,Fin.val_add,Fin.val_one,Nat.mod_eq_of_lt (show 1<n+2 by omega)]

def orderedCycleAtPositionEquiv {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (i:Fin (n+2)):
    OrderedCycleRepresentations H (n+2)≃DirectedEdges H:=
  (orderedCycleReparametrise H (n+2) (Equiv.addLeft i) (cycleGraph_add_left_adj n i)).trans
    (orderedCycleFirstEdgeEquiv H n hn hH)

theorem orderedCycleAtPositionEquiv_value {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (i:Fin (n+2))
    (f:OrderedCycleRepresentations H (n+2)):
    (orderedCycleAtPositionEquiv H n hn hH i f).val=(f.val i,f.val (cycleNext i)):=by
  change (orderedCycleFirstEdge H n (orderedCycleReparametrise H (n+2) (Equiv.addLeft i) (cycleGraph_add_left_adj n i) f)).val = _
  simp [orderedCycleReparametrise,orderedCycleFirstEdge,cycleNext_eq_add_one]

theorem orderedCycle_position_fibre_unique {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (i:Fin (n+2)) (x y:V) (hxy:H.Adj x y):
    ∃! f:OrderedCycleRepresentations H (n+2),f.val i=x ∧ f.val (cycleNext i)=y:=by
  let e:=orderedCycleAtPositionEquiv H n hn hH i
  let a:DirectedEdges H:=⟨(x,y),hxy⟩
  refine ⟨e.symm a,?_,?_⟩
  · have h:=congrArg Subtype.val (e.apply_symm_apply a)
    rw [orderedCycleAtPositionEquiv_value] at h
    exact Prod.mk.inj h
  · intro f hf
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    change (e f).val=(x,y)
    rw [orderedCycleAtPositionEquiv_value]
    exact Prod.ext hf.1 hf.2

theorem orderedCycle_position_vertex_card {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (i:Fin (n+2)) (x:V):
    Fintype.card {f:OrderedCycleRepresentations H (n+2) // f.val i=x}=H.degree x:=by
  let rot:=orderedCycleReparametrise H (n+2) (Equiv.addLeft i) (cycleGraph_add_left_adj n i)
  have hrot (f:OrderedCycleRepresentations H (n+2)):(rot f).val 0=f.val i:=by
    simp [rot,orderedCycleReparametrise]
  let e:{f:OrderedCycleRepresentations H (n+2) // f.val i=x}≃OrderedCycleAtVertex H n x:=
    Equiv.subtypeEquiv rot (fun f=>by simpa [OrderedCycleAtVertex,hrot f])
  exact (Fintype.card_congr e).trans (ordered_cycle_first_vertex_card H n hn hH x)
end Oberwolfach
