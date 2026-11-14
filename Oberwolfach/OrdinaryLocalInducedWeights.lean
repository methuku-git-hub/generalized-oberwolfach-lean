module

public import Oberwolfach.OrdinaryLocalInducedVertices
public import Oberwolfach.OrdinaryLocalLoads

@[expose] public section
/-! Induced-domain weights transfer to the ambient inner host with exactly
the same local weighted vertex degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_induced_weighted_degree (Q F:SimpleGraph V) (A T:Finset V) (hTA:T⊆A)
    (w:LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T) r→ℝ)
    (v:V) (hv:v∈T):
    hypergraphWeightedDegree localOrdinaryVertices
      (fun C:LocalOrdinaryCycle (spanningRestriction Q A) F T r=>w ((ordinaryLocalInducedEquiv Q F A T hTA).symm C)) v=
    hypergraphWeightedDegree localOrdinaryVertices w ⟨v,hTA hv⟩:=by
  let e:=ordinaryLocalInducedEquiv (r:=r) Q F A T hTA
  have hmem (C:LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T) r):
      v∈localOrdinaryVertices (e C)↔(⟨v,hTA hv⟩:{v:V // v∈A})∈localOrdinaryVertices C:=by
    rw [ordinary_local_induced_equiv_vertices]
    constructor
    · intro hh
      obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hh
      have he:x=(⟨v,hTA hv⟩:{v:V // v∈A}):=Subtype.ext hxv
      simpa only [he] using hx
    · intro hh
      exact Finset.mem_image.mpr ⟨⟨v,hTA hv⟩,hh,rfl⟩
  have hs:=e.sum_comp (fun C=>if v∈localOrdinaryVertices C then w (e.symm C) else 0)
  unfold hypergraphWeightedDegree
  simpa only [e,hmem,Equiv.symm_apply_apply] using hs.symm
end Oberwolfach
