module

public import Oberwolfach.OrdinaryProtectedPairBalanceAgreement

@[expose] public section
/-! Removing the same protected reservoir preserves exact agreement on the
protected pair, even if the hosts differ elsewhere. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_pair_reserve_agreement
    (R G:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (Inner:Finset V) (Hubs:Finset U)
    (hr:∀v∈Inner,∀w∈Inner,R.Adj v w↔G.Adj v w)
    (hs:∀v∈Inner,∀u∈Hubs,J v u↔H v u)
    (hK:Disjoint K (ordinaryRootResources Inner Hubs)):
    (∀v∈Inner,∀w∈Inner,
      (R\ordinaryResourceRim R K).Adj v w↔(G\ordinaryResourceRim G K).Adj v w) ∧
    (∀v∈Inner,∀u∈Hubs,
      (J v u∧¬(Sum.inr (v,u)∈K))↔(H v u∧¬(Sum.inr (v,u)∈K))) :=by
  obtain ⟨hRim,hSpoke⟩:=ordinaryRootResources_avoid K Inner Hubs hK
  constructor
  · intro v hv w hw
    have hn:=hRim v hv w hw
    change (R.Adj v w∧¬(R.Adj v w∧Sum.inl s(v,w)∈K))↔
      (G.Adj v w∧¬(G.Adj v w∧Sum.inl s(v,w)∈K))
    simpa [hn] using hr v hv w hw
  · intro v hv u hu
    have hn:=hSpoke v hv u hu
    simpa [hn] using hs v hv u hu
end Oberwolfach
