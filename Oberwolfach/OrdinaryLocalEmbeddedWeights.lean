module

public import Oberwolfach.OrdinaryLocalCycleEmbeddingEquiv
public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section
/-! Fixed local cycle weights keep their vertex loads under an injective
embedding of the entire factor domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] {r:ℕ}

theorem ordinary_local_embedded_weighted_degree (e:V↪W) (Q F:SimpleGraph V) (T:Finset V)
    (w:LocalOrdinaryCycle Q F T r→ℝ) (v:V):
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle (Q.map e) (F.map e) (T.image e) r=>
        w ((ordinaryLocalCycleEmbeddingEquiv e Q F T).symm C)) (e v)=
    hypergraphWeightedDegree localOrdinaryVertices w v:=by
  let g:=ordinaryLocalCycleEmbeddingEquiv (r:=r) e Q F T
  have hmem (C:LocalOrdinaryCycle Q F T r):e v∈localOrdinaryVertices (g C)↔v∈localOrdinaryVertices C:=by
    change e v∈localOrdinaryVertices (ordinaryLocalCycleMap e Q F T C)↔_
    rw [ordinary_local_cycle_map_vertices]
    simp [e.injective.eq_iff]
  have hs:=g.sum_comp (fun C=>if e v∈localOrdinaryVertices C then w (g.symm C) else 0)
  unfold hypergraphWeightedDegree
  simpa only [g,hmem,Equiv.symm_apply_apply] using hs.symm
end Oberwolfach
