module

public import Oberwolfach.CycleGraphSymmetries
public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section
/-! Every directed edge of an embedded cycle is the first directed edge of
an ordered representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordered_cycle_representation_first_edge_exists {V:Type} [Fintype V] [DecidableEq V]
    (n:ℕ) (f:Fin (n+2)↪V) (x y:V)
    (hxy:((SimpleGraph.cycleGraph (n+2)).map f).Adj x y):
    ∃ g:Fin (n+2)↪V,(SimpleGraph.cycleGraph (n+2)).map g=(SimpleGraph.cycleGraph (n+2)).map f ∧ g 0=x ∧ g 1=y:=by
  rw [SimpleGraph.map_adj] at hxy
  obtain ⟨i,j,hij,hix,hjy⟩:=hxy
  rw [SimpleGraph.cycleGraph_adj] at hij
  rcases hij with hrev|hfwd
  · have hj:i-1=j:=by
      calc
        _ = i-(i-j):=by rw [hrev]
        _ = j:=by abel
    let e:Equiv.Perm (Fin (n+2)):=Equiv.subLeft i
    let g:Fin (n+2)↪V:=e.toEmbedding.trans f
    refine ⟨g,?_,?_,?_⟩
    · change (SimpleGraph.cycleGraph (n+2)).map (f ∘ e)=_
      rw [←SimpleGraph.map_map]
      change ((SimpleGraph.cycleGraph (n+2)).map (Equiv.subLeft i).toEmbedding).map f = _
      rw [cycleGraph_map_reflection]
    · simpa [g,e] using hix
    · simpa [g,e,hj] using hjy
  · have hj:i+1=j:=by
      calc
        _ = i+(j-i):=by rw [hfwd]
        _ = j:=by abel
    let e:Equiv.Perm (Fin (n+2)):=Equiv.addLeft i
    let g:Fin (n+2)↪V:=e.toEmbedding.trans f
    refine ⟨g,?_,?_,?_⟩
    · change (SimpleGraph.cycleGraph (n+2)).map (f ∘ e)=_
      rw [←SimpleGraph.map_map]
      change ((SimpleGraph.cycleGraph (n+2)).map (Equiv.addLeft i).toEmbedding).map f = _
      rw [cycleGraph_map_translation]
    · simpa [g,e] using hix
    · simpa [g,e,hj] using hjy
end Oberwolfach
