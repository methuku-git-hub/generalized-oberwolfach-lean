module

public import Oberwolfach.OrdinaryUniformProtectedReservoirEvent

@[expose] public section
/-! A reservoir selected before correction survives every correction that
protects its occupied rows and hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reservoir_survives_protected_correction
    (Q JQ:SimpleGraph V) (H JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (T:Finset V) (B:Finset U) (hK:K⊆ordinaryHostResources Q H)
    (hT:ordinaryResourceRows K⊆T) (hB:ordinaryResourceHubs K⊆B)
    (hJQ:∀v∈T,∀w∈T,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈T ∧ u∈B)):
    K⊆ordinaryHostResources (Q\JQ) (fun v u=>H v u∧¬JH v u):=by
  intro e he
  cases e with
  | inl e=>
    induction e using Sym2.inductionOn with
    | _ v w=>
      have hv:v∈T:=hT (Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩)
      have hw:w∈T:=hT (Finset.mem_biUnion.mpr ⟨Sum.inl s(v,w),he,by simp⟩)
      apply (ordinaryHostResources_rim _ _ _).mpr
      exact ⟨(ordinaryHostResources_rim Q H _).mp (hK he),hJQ v hv w hw⟩
  | inr p=>
    rcases p with ⟨v,u⟩
    have hv:v∈T:=hT (Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩)
    have hu:u∈B:=hB (Finset.mem_biUnion.mpr ⟨Sum.inr (v,u),he,by simp⟩)
    apply (ordinaryHostResources_spoke _ _ v u).mpr
    exact ⟨(ordinaryHostResources_spoke Q H v u).mp (hK he),fun hj=>hJH v u hj ⟨hv,hu⟩⟩

theorem ordinary_uniform_reservoir_before_protected_correction
    (r m t f a b:ℕ) (ε:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (hRes:OrdinaryUniformProtectedReservoirEvent r m t f a b ε Q F H)
    (A Z Wterm W:Finset V) (Bterm B:Finset U)
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤ε*Fintype.card V)
    (hsize:Wterm.card+Bterm.card≤t) (hWW:Wterm⊆W) (hBB:Bterm⊆B)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f):
    ∃K:Finset (Sym2 V⊕(V×U)),K⊆ordinaryHostResources Q H ∧
      Disjoint K (ordinaryRootResources Z B) ∧
      (ordinaryResourceRows K).card≤2^(t*t)*a ∧ (ordinaryResourceHubs K).card≤2^(t*t)*b ∧
      ordinaryResourceRows K⊆Wterm∪A ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) K ∧
      (∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) K) ∧
      ∀(T:Finset V) (B':Finset U),ordinaryResourceRows K⊆T → ordinaryResourceHubs K⊆B' →
      ∀(JQ:SimpleGraph V) (JH:V→U→Prop),
        (∀v∈T,∀w∈T,¬JQ.Adj v w)→
        (∀v u,JH v u→¬(v∈T ∧ u∈B'))→
        K⊆ordinaryHostResources (Q\JQ) (fun v u=>H v u∧¬JH v u):=by
  obtain ⟨K,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs⟩:=hRes A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB
  refine ⟨K,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,?_⟩
  intro T B' hT hB' JQ JH hJQ hJH
  exact ordinary_reservoir_survives_protected_correction Q JQ H JH K T B' hK hT hB' hJQ hJH
end Oberwolfach
