module

public import Oberwolfach.OrdinaryLocalInducedVertices
public import Oberwolfach.OrdinaryLocalRestriction

@[expose] public section
/-! Cycles on an induced vertex domain lift injectively to the ambient
local cycle family, with exactly their vertices mapped by subtype value. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

def ordinaryFullInducedCycleEmbedding (Q F:SimpleGraph V) (T:Finset V):
    LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V)) Finset.univ r ↪
      LocalOrdinaryCycle Q F T r:=by
  have hD:ordinaryInducedLocalDomain T T=Finset.univ:=by
    ext v
    simp [ordinaryInducedLocalDomain]
  let g:=Equiv.cast (congrArg (fun D=>LocalOrdinaryCycle (Q.induce (T:Set V))
    (F.induce (T:Set V)) D r) hD.symm)
  let e:=ordinaryLocalInducedEquiv (r:=r) Q F T T (Finset.Subset.rfl)
  let hQ:spanningRestriction Q T≤Q:=fun a b h=>(spanningRestriction_adj Q T a b).mp h |>.1
  exact g.toEmbedding.trans (e.toEmbedding.trans (localOrdinaryRestrictionParent hQ (Finset.Subset.rfl)))

theorem ordinary_full_induced_cycle_embedding_vertices (Q F:SimpleGraph V) (T:Finset V)
    (C:LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V)) Finset.univ r):
    localOrdinaryVertices (ordinaryFullInducedCycleEmbedding Q F T C)=
      (localOrdinaryVertices C).image Subtype.val:=by
  have hD:ordinaryInducedLocalDomain T T=Finset.univ:=by
    ext v
    simp [ordinaryInducedLocalDomain]
  let hc:=congrArg (fun D=>LocalOrdinaryCycle (Q.induce (T:Set V))
    (F.induce (T:Set V)) D r) hD.symm
  have hv:=ordinary_local_vertices_cast_domain (Q.induce (T:Set V)) (F.induce (T:Set V))
    Finset.univ (ordinaryInducedLocalDomain T T) hD.symm hc C
  have hh:=ordinary_local_induced_equiv_vertices (r:=r) Q F T T (Finset.Subset.rfl) (cast hc C)
  change localOrdinaryVertices ((ordinaryLocalInducedEquiv Q F T T (Finset.Subset.rfl)) (cast hc C)) = _
  rw [hh,hv]
end Oberwolfach
