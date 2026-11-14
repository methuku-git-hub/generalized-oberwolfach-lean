module

public import Oberwolfach.CycleGraphFixTwo

@[expose] public section
/-! Translation and reversal preserve the cycle graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_add_left_adj (n:ℕ) (a i j:Fin (n+2)):
    (SimpleGraph.cycleGraph (n+2)).Adj (a+i) (a+j) ↔ (SimpleGraph.cycleGraph (n+2)).Adj i j:=by
  have hsub (i j a:Fin (n+2)):(a+i)-(a+j)=i-j:=by abel
  simp only [SimpleGraph.cycleGraph_adj,hsub]

theorem cycleGraph_sub_left_adj (n:ℕ) (a i j:Fin (n+2)):
    (SimpleGraph.cycleGraph (n+2)).Adj (a-i) (a-j) ↔ (SimpleGraph.cycleGraph (n+2)).Adj i j:=by
  have hsub (i j a:Fin (n+2)):(a-i)-(a-j)=j-i:=by abel
  simp only [SimpleGraph.cycleGraph_adj,hsub,or_comm]

theorem cycleGraph_map_equiv_of_adj {r:ℕ} (e:Equiv.Perm (Fin r))
    (h:∀ i j,(SimpleGraph.cycleGraph r).Adj (e i) (e j) ↔ (SimpleGraph.cycleGraph r).Adj i j):
    (SimpleGraph.cycleGraph r).map e.toEmbedding=SimpleGraph.cycleGraph r:=by
  ext u v
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨i,j,hij,rfl,rfl⟩
    exact (h i j).mpr hij
  · intro huv
    refine ⟨e.symm u,e.symm v,?_,by simp,by simp⟩
    apply (h _ _).mp
    simpa using huv

theorem cycleGraph_map_translation (n:ℕ) (a:Fin (n+2)):
    (SimpleGraph.cycleGraph (n+2)).map (Equiv.addLeft a).toEmbedding=SimpleGraph.cycleGraph (n+2):=by
  apply cycleGraph_map_equiv_of_adj
  exact cycleGraph_add_left_adj n a

theorem cycleGraph_map_reflection (n:ℕ) (a:Fin (n+2)):
    (SimpleGraph.cycleGraph (n+2)).map (Equiv.subLeft a).toEmbedding=SimpleGraph.cycleGraph (n+2):=by
  apply cycleGraph_map_equiv_of_adj
  exact cycleGraph_sub_left_adj n a
end Oberwolfach
