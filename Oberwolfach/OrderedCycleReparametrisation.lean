module

public import Oberwolfach.OrderedCycleRepresentationEdges

@[expose] public section
/-! Reparametrising an ordered cycle by a graph automorphism permutes its
representations without changing the physical cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

private theorem orderedCycle_map_precompose {V:Type} {r:ℕ}
    (e:Equiv.Perm (Fin r)) (f:Fin r↪V)
    (h:(SimpleGraph.cycleGraph r).map e.toEmbedding=SimpleGraph.cycleGraph r):
    (SimpleGraph.cycleGraph r).map (e.toEmbedding.trans f)=(SimpleGraph.cycleGraph r).map f:=by
  change (SimpleGraph.cycleGraph r).map (f ∘ e)=_
  rw [←SimpleGraph.map_map]
  change ((SimpleGraph.cycleGraph r).map e.toEmbedding).map f = _
  rw [h]

def orderedCycleReparametrise {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V) (r:ℕ)
    (e:Equiv.Perm (Fin r))
    (h:∀ i j,(SimpleGraph.cycleGraph r).Adj (e i) (e j) ↔ (SimpleGraph.cycleGraph r).Adj i j):
    OrderedCycleRepresentations H r≃OrderedCycleRepresentations H r:=by
  have he:(SimpleGraph.cycleGraph r).map e.toEmbedding=SimpleGraph.cycleGraph r:=cycleGraph_map_equiv_of_adj e h
  have heinv:(SimpleGraph.cycleGraph r).map e.symm.toEmbedding=SimpleGraph.cycleGraph r:=by
    apply cycleGraph_map_equiv_of_adj
    intro i j
    have hh:=h (e.symm i) (e.symm j)
    simpa using hh.symm
  refine {toFun:=fun f=>⟨e.toEmbedding.trans f.val,?_⟩
          invFun:=fun f=>⟨e.symm.toEmbedding.trans f.val,?_⟩
          left_inv:=?_
          right_inv:=?_}
  · apply f.property.trans ?_
    symm
    change (SimpleGraph.cycleGraph r).map (f.val ∘ e) = _
    rw [←SimpleGraph.map_map]
    change ((SimpleGraph.cycleGraph r).map e.toEmbedding).map f.val = _
    rw [he]
  · apply f.property.trans ?_
    symm
    change (SimpleGraph.cycleGraph r).map (f.val ∘ e.symm) = _
    rw [←SimpleGraph.map_map]
    change ((SimpleGraph.cycleGraph r).map e.symm.toEmbedding).map f.val = _
    rw [heinv]
  · intro f
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    simp
  · intro f
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    simp
end Oberwolfach
