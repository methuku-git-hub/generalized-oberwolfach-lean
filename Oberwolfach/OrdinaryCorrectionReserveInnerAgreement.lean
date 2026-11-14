module

public import Oberwolfach.OrdinaryCorrectedProtectedReservoir
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! The correction and protected reservoir leave every smaller inner pair
unchanged. This removes their ambient-size edit cost at later levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_correction_reserve_inner_agreement
    (R JQ:SimpleGraph V) (H JH:V→U→Prop) (Z:Finset V) (B:Finset U)
    (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Z,∀w∈Z,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Z ∧ u∈B))
    (hK:Disjoint K (ordinaryRootResources Z B)):
    let G:=(R\JQ)\ordinaryResourceRim (R\JQ) K
    let Hs:=fun v u=>H v u∧¬JH v u∧¬(Sum.inr (v,u)∈K);
    (∀v∈Z,∀w∈Z,G.Adj v w↔R.Adj v w) ∧
    (∀v∈Z,∀u∈B,Hs v u↔H v u) ∧
    ∀(X:Finset V) (Y:Finset U),X⊆Z→Y⊆B→
      G.induce (X:Set V)=R.induce (X:Set V) ∧
      (fun (v:X) (u:Y)=>Hs v.val u.val)=(fun (v:X) (u:Y)=>H v.val u.val) :=by
  intro G Hs
  have hRim:∀v∈Z,∀w∈Z,¬Sum.inl s(v,w)∈K:=by
    intro v hv w hw he
    exact Finset.disjoint_left.mp hK he (ordinaryRootResources_rim Z B v w hv hw)
  have hSpoke:∀v∈Z,∀u∈B,¬Sum.inr (v,u)∈K:=by
    intro v hv u hu he
    exact Finset.disjoint_left.mp hK he (ordinaryRootResources_spoke Z B v u hv hu)
  have hgraph:∀v∈Z,∀w∈Z,G.Adj v w↔R.Adj v w:=by
    intro v hv w hw
    change ((R.Adj v w ∧ ¬JQ.Adj v w) ∧ ¬((R.Adj v w ∧ ¬JQ.Adj v w) ∧ Sum.inl s(v,w)∈K)) ↔ R.Adj v w
    exact ⟨fun h=>h.1.1,fun h=>⟨⟨h,hJQ v hv w hw⟩,fun hk=>hRim v hv w hw hk.2⟩⟩
  have hspokes:∀v∈Z,∀u∈B,Hs v u↔H v u:=by
    intro v hv u hu
    change (H v u ∧ ¬JH v u ∧ ¬Sum.inr (v,u)∈K) ↔ H v u
    exact ⟨fun h=>h.1,fun h=>⟨h,fun hj=>hJH v u hj ⟨hv,hu⟩,hSpoke v hv u hu⟩⟩
  refine ⟨hgraph,hspokes,?_⟩
  intro X Y hX hY
  constructor
  · ext v w
    exact hgraph v.val (hX v.property) w.val (hX w.property)
  · funext v u
    exact propext (hspokes v.val (hX v.property) u.val (hY u.property))
end Oberwolfach
