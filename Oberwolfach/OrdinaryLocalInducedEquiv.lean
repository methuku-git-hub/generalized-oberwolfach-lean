module

public import Oberwolfach.OrdinaryLocalCycleEmbeddingEquiv
public import Oberwolfach.OrdinaryLocalConflictEquiv
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! Local cycles inside a vertex set are equivalent to local cycles of the
induced graph; ambient conflicts agree on that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

def ordinaryInducedLocalDomain (A T:Finset V):Finset {v:V // v∈A}:=
  Finset.univ.filter (fun v=>v.val∈T)

theorem ordinary_induced_local_domain_image (A T:Finset V) (hTA:T⊆A):
    (ordinaryInducedLocalDomain A T).image (Subtype.val:{v:V // v∈A}→V)=T:=by
  ext v
  constructor
  · intro hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hx).2
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v,hTA hv⟩,by simp [ordinaryInducedLocalDomain,hv],rfl⟩

def ordinaryLocalInducedEquiv (Q F:SimpleGraph V) (A T:Finset V) (hTA:T⊆A):
    LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T) r ≃
    LocalOrdinaryCycle (spanningRestriction Q A) F T r:=by
  let e:{v:V // v∈A}↪V:=Function.Embedding.subtype (fun x=>x∈(A:Set V))
  have hT:(ordinaryInducedLocalDomain A T).image e=T:=ordinary_induced_local_domain_image A T hTA
  have hconf:∀v∈T,∀w∈T,(spanningRestriction F A).Adj v w↔F.Adj v w:=by
    intro v hv w hw
    simp [spanningRestriction_adj,hTA hv,hTA hw]
  have g:LocalOrdinaryCycle (Q.induce (A:Set V)) (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T) r ≃
      LocalOrdinaryCycle (spanningRestriction Q A) (spanningRestriction F A) T r:=by
    have hc:LocalOrdinaryCycle ((Q.induce (A:Set V)).map e) ((F.induce (A:Set V)).map e)
        ((ordinaryInducedLocalDomain A T).image e) r=
        LocalOrdinaryCycle (spanningRestriction Q A) (spanningRestriction F A) T r:=by
      rw [hT]
      rfl
    exact (ordinaryLocalCycleEmbeddingEquiv (r:=r) e (Q.induce (A:Set V))
      (F.induce (A:Set V)) (ordinaryInducedLocalDomain A T)).trans (Equiv.cast hc)
  exact g.trans (ordinaryLocalConflictEquiv (spanningRestriction Q A) (spanningRestriction F A) F T hconf)
end Oberwolfach
