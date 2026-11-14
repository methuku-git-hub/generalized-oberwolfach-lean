module

public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section
/-! Successive resource decompositions retain their original host and
all-pairs conflict condition when the removed wheels are joined. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sequential_host_decompositions
    (Q A B C F:SimpleGraph V) (H S T W:V→U→Prop) (r:ℕ)
    (hA:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A S))
    (hB:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources B T))
    (hC:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources C W))
    (hBsub:B≤Q\A) (hTsub:∀v u,T v u→H v u∧¬S v u)
    (hCsub:C≤(Q\A)\B) (hWsub:∀v u,W v u→(H v u∧¬S v u)∧¬T v u):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources ((A⊔B)⊔C) (fun v u=>(S v u∨T v u)∨W v u)):=by
  have hab:Disjoint A B:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hBsub hvw.2).2 hvw.1
  have hst:∀v u,¬(S v u∧T v u):=by
    rintro v u ⟨hs,ht⟩
    exact (hTsub v u ht).2 hs
  have habc:Disjoint (A⊔B) C:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hh:=hCsub hvw.2
    rcases hvw.1 with ha|hb
    · exact hh.1.2 ha
    · exact hh.2 hb
  have hstw:∀v u,¬((S v u∨T v u)∧W v u):=by
    rintro v u ⟨hs|ht,hw⟩
    · exact (hWsub v u hw).1.2 hs
    · exact (hWsub v u hw).2 ht
  have habres:=resource_decomposition_union _ _ _ hA hB (ordinaryHostResources_disjoint A B S T hab hst)
  rw [←ordinaryHostResources_union] at habres
  have hall:=resource_decomposition_union _ _ _ habres hC
    (ordinaryHostResources_disjoint (A⊔B) C (fun v u=>S v u∨T v u) W habc hstw)
  rwa [←ordinaryHostResources_union] at hall
end Oberwolfach
