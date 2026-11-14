module

public import Oberwolfach.OrderedCycleRepresentationCount

@[expose] public section
/-! Exactly d_H(x) ordered cycle representations begin at x. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev OrderedCycleAtVertex {V:Type} (H:SimpleGraph V) (n:ℕ) (x:V):=
  {f:OrderedCycleRepresentations H (n+2) // f.val 0=x}

def orderedCycleFirstNeighbour {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V) (n:ℕ) (x:V)
    (f:OrderedCycleAtVertex H n x):H.neighborSet x:=by
  refine ⟨f.val.val 1,?_⟩
  have h: H.Adj (f.val.val 0) (f.val.val 1):=(orderedCycleFirstEdge H n f.val).property
  simpa [f.property] using h

theorem orderedCycleFirstNeighbour_bijective {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (x:V):
    Function.Bijective (orderedCycleFirstNeighbour H n x):=by
  constructor
  · intro f g h
    apply Subtype.ext
    apply orderedCycleFirstEdge_injective H n hn
    apply Subtype.ext
    apply Prod.ext
    · exact f.property.trans g.property.symm
    · exact congrArg Subtype.val h
  · intro y
    let e:DirectedEdges H:=⟨(x,y.val),y.property⟩
    let eqv:=orderedCycleFirstEdgeEquiv H n hn hH
    let f:=eqv.symm e
    have he:orderedCycleFirstEdge H n f=e:=eqv.apply_symm_apply e
    have h0:f.val 0=x:=congrArg Prod.fst (congrArg Subtype.val he)
    have h1:f.val 1=y.val:=congrArg Prod.snd (congrArg Subtype.val he)
    refine ⟨⟨f,h0⟩,?_⟩
    apply Subtype.ext
    exact h1

theorem ordered_cycle_first_vertex_card {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V)
    (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)) (x:V):
    Fintype.card (OrderedCycleAtVertex H n x)=H.degree x:=by
  have h:=Fintype.card_congr (Equiv.ofBijective (orderedCycleFirstNeighbour H n x)
    (orderedCycleFirstNeighbour_bijective H n hn hH x))
  simpa only [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card] using h
end Oberwolfach
