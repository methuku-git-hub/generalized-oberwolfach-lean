module

public import Oberwolfach.OrdinaryLocalConflictEquiv
public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section
/-! Equivalent conflict graphs on the local domain preserve all fixed
cycle-weight loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_conflict_weighted_degree (Q F F':SimpleGraph V) (T:Finset V)
    (h:∀v∈T,∀w∈T,F.Adj v w↔F'.Adj v w) (wt:LocalOrdinaryCycle Q F T r→ℝ) (v:V):
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle Q F' T r=>wt ((ordinaryLocalConflictEquiv Q F F' T h).symm C)) v=
    hypergraphWeightedDegree localOrdinaryVertices wt v:=by
  let e:=ordinaryLocalConflictEquiv (r:=r) Q F F' T h
  have hs:=e.sum_comp (fun C=>if v∈localOrdinaryVertices C then wt (e.symm C) else 0)
  unfold hypergraphWeightedDegree
  simpa only [e,Equiv.symm_apply_apply,ordinary_local_conflict_equiv_vertices] using hs.symm
end Oberwolfach
