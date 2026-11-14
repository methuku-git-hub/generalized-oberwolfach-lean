module

public import Oberwolfach.OrdinaryCorrectedProtectedReservoir

@[expose] public section
/-! Extract a single correction and its reservoir without losing the
terminal absorption guarantee. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_corrected_reservoir_witness
    (r m t a b:ℕ) (ξ:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A Z Wterm:Finset V) (Bterm B:Finset U)
    (hRes:OrdinaryCorrectedProtectedReservoir r m t a b ξ Q F H A Z Wterm Bterm B):
    ∃(K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop),
      K⊆ordinaryHostResources Q H ∧ Disjoint K (ordinaryRootResources Z B) ∧
      (ordinaryResourceRows K).card≤2^(t*t)*a ∧ (ordinaryResourceHubs K).card≤2^(t*t)*b ∧
      ordinaryResourceRows K⊆Wterm∪A ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) K ∧
      (∀(G:SimpleGraph V) (Hs:V→U→Prop),ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) K) ∧
      JQ≤Q ∧ (∀v∈Z,∀w∈Z,¬JQ.Adj v w) ∧
      (∀v u,JH v u→H v u ∧ ¬(v∈Z ∧ u∈B)) ∧
      K⊆ordinaryHostResources (Q\JQ) (fun v u=>H v u∧¬JH v u) ∧
      (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
      (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  obtain ⟨K,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,JQ,JH,hJQ,hJQavoid,hJH,hprotect,hbal,hdiv,hrow,hcol⟩:=hRes
  exact ⟨K,JQ,JH,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,hJQ,hJQavoid,hJH,hprotect,hbal,hdiv,hrow,hcol⟩
end Oberwolfach
