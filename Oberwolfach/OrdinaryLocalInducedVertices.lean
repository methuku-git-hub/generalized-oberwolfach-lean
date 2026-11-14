module

public import Oberwolfach.OrdinaryLocalInducedEquiv

@[expose] public section
/-! The induced-domain cycle equivalence retains the same ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_local_vertices_cast_domain (Q F:SimpleGraph V) (S T:Finset V)
    (h:S=T) (hc:LocalOrdinaryCycle Q F S r=LocalOrdinaryCycle Q F T r)
    (C:LocalOrdinaryCycle Q F S r):localOrdinaryVertices (cast hc C)=localOrdinaryVertices C:=by
  subst T
  have hh:hc=rfl:=Subsingleton.elim _ _
  cases hh
  rfl

theorem ordinary_local_induced_equiv_vertices (Q F:SimpleGraph V) (A T:Finset V) (hTA:T⊆A)
    (C:LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T) r):
    localOrdinaryVertices (ordinaryLocalInducedEquiv Q F A T hTA C)=
      (localOrdinaryVertices C).image Subtype.val:=by
  simp only [ordinaryLocalInducedEquiv,Equiv.trans_apply,ordinary_local_conflict_equiv_vertices,
    ordinaryLocalCycleEmbeddingEquiv,Equiv.ofBijective_apply,Equiv.cast_apply]
  rw [ordinary_local_vertices_cast_domain _ _ _ _ (ordinary_induced_local_domain_image A T hTA)]
  exact ordinary_local_cycle_map_vertices _ _ _ _ C
end Oberwolfach
