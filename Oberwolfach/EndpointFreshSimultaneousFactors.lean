module

public import Oberwolfach.EndpointFreshDomainsCommonEvent
public import Oberwolfach.EndpointFactorSelection

@[expose] public section

/-! Actual simultaneous endpoint triangle factors on the common physical
sample. Exact final class ratios and deletion budgets are checked at the
caller, and the returned objects retain their original endpoint records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_fresh_simultaneous_factors (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
      ∀ (V E:Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E],∀ L:ℕ,
      N≤Fintype.card V→L≤Fintype.card V→
      ∀ (Q F:SimpleGraph V) (S T:Fin L→Finset V) (f:Fin L→V↪E) (hST:∀ j,Disjoint (S j) (T j)),
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ j,EndpointNeighbourCounts Q F (S j) (T j) (γ*Fintype.card V))→
      ∀ wt:∀ j,EndpointTriangle Q F (S j) (T j)→ℝ,
      (∀ j C,b/(Fintype.card V:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^2)→
      (∀ j,∀ v∈S j∪T j,|1-hypergraphWeightedDegree endpointTriangleVertices (wt j) v|≤η)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Fin L→Finset V,(∀ i,Y i⊆S i∪T i)→
            (∀ i,(Y i∩S i).card=2*(Y i∩T i).card)→
            (∀ i,(((((S i∪T i).filter (fun v=>σ (f i v)=true))\Y i).card+
              (Y i\((S i∪T i).filter (fun v=>σ (f i v)=true))).card:ℕ):ℝ)≤ζ*(p*(T i).card))→
            (∀ i j,i≠j→((Y i∩Y j).card:ℝ)≤ρ^2*Fintype.card V)→
            (∀ v,((Finset.univ.filter (fun i=>v∈Y i)).card:ℝ)≤ρ*Fintype.card V)→
            (∀ i,2*(ρ*Real.sqrt ρ*Fintype.card V)+
              2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card V)):ℝ)≤ζ*(p*(T i).card))→
            ∃ D:∀ i,Finset (EndpointTriangle Q F (S i) (T i)),
              (∀ i,(∀ C∈D i,∀ E∈D i,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
                (D i).biUnion endpointTriangleVertices=Y i) ∧
              (∀ i j,i≠j→Disjoint (endpointFactorGraph (hST i) (D i)) (endpointFactorGraph (hST j) (D j))) ∧
              ∀ v,((⨆ i,endpointFactorGraph (hST i) (D i)).degree v:ℝ)≤2*(ρ*Fintype.card V)):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=endpoint_fresh_domains_common_event γ b B hγ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 q
  obtain ⟨Ns,hNs⟩:=select_endpoint_factors ρ hρ
  refine ⟨max Nf Ns,?_⟩
  intro V E _ _ _ _ L hn hL Q F S T f hST hF hcommon wt hw herr
  have hh:=hNf V (Fin L) E (by omega) (by simpa only [Fintype.card_fin] using hL)
    Q F S T f hST hF hcommon wt hw herr
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYU hratio hchange hinter hmem hbudget
  apply hNs V (by omega) L Q F S T Y hST hinter hmem
  intro i K _hK hdeg
  exact hσ i (Y i) (hYU i) (hratio i) (hchange i) K (fun v=>(hdeg v).trans (hbudget i))

end Oberwolfach
