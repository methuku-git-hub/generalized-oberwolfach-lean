module

public import Oberwolfach.OrdinaryLocalAugmentCycles
public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section
/-! Transfer fixed local weights through the exact cycle equivalence,
preserving each vertex load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_augment_weighted_degree (Q F:SimpleGraph V) (T:Finset V)
    (w:LocalOrdinaryCycle Q F T r→ℝ) (v:V):
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle (ordinaryLocalHostAugment Q T) F T r=>w ((ordinaryLocalAugmentEquiv Q F T).symm C)) v=
    hypergraphWeightedDegree localOrdinaryVertices w v:=by
  let e:=ordinaryLocalAugmentEquiv (r:=r) Q F T
  have hs:=e.sum_comp (fun C=>if v∈localOrdinaryVertices C then w (e.symm C) else 0)
  unfold hypergraphWeightedDegree
  simpa only [e,Equiv.symm_apply_apply,ordinary_local_augment_vertices] using hs.symm
end Oberwolfach
