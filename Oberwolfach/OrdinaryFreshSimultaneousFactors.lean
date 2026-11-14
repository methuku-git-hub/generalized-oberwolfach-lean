module

public import Oberwolfach.OrdinaryFreshDomainsCommonEvent
public import Oberwolfach.LocalFactorSelection

@[expose] public section

/-! Actual simultaneous ordinary boundary-factor choices on one raw
physical-coordinate event. Every factor is constructed from parent weights
and common-neighbourhood bounds; no single-copy existence oracle is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_simultaneous_factors (m:ℕ) (hm:2≤m) (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
      ∀ (V E:Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E],∀ L:ℕ,
      N≤Fintype.card V→L≤Fintype.card V→
      ∀ (Q F:SimpleGraph V) (T:Fin L→Finset V) (f:Fin L→V↪E),
      (∀ j,κ*Fintype.card V≤((T j).card:ℝ))→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ j,∀ X:Finset V,X.card≤(if m=2 then 3 else 2)→
        γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ))→
      ∀ wt:∀ j,LocalOrdinaryCycle Q F (T j) (m+1)→ℝ,
      (∀ j C,b/(Fintype.card V:ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^m)→
      (∀ j,∀ v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Fin L→Finset V,(∀ i,Y i⊆T i)→(∀ i,(m+1)∣(Y i).card)→
            (∀ i,(((((T i).filter (fun v=>σ (f i v)=true))\Y i).card+
              (Y i\((T i).filter (fun v=>σ (f i v)=true))).card:ℕ):ℝ)≤ζ*(p*(T i).card))→
            (∀ i j,i≠j→((Y i∩Y j).card:ℝ)≤ρ^2*Fintype.card V)→
            (∀ v,((Finset.univ.filter (fun i=>v∈Y i)).card:ℝ)≤ρ*Fintype.card V)→
            (∀ i,2*(ρ*Real.sqrt ρ*Fintype.card V)+
              2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card V)):ℝ)≤ζ*(p*(T i).card))→
            ∃ D:∀ i,Finset (LocalOrdinaryCycle Q F (T i) (m+1)),
              (∀ i,(∀ C∈D i,∀ E∈D i,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
                (D i).biUnion localOrdinaryVertices=Y i) ∧
              (∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (D i)) (localOrdinaryFactorGraph (D j))) ∧
              ∀ v,((⨆ i,localOrdinaryFactorGraph (D i)).degree v:ℝ)≤2*(ρ*Fintype.card V)):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_domains_common_event m hm γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 q
  obtain ⟨Ns,hNs⟩:=select_local_ordinary_factors ρ hρ
  refine ⟨max Nf Ns,?_⟩
  intro V E _ _ _ _ L hn hL Q F T f hsize hF hcommon wt hw herr
  have hh:=hNf V (Fin L) E (by omega) (by simpa only [Fintype.card_fin] using hL)
    Q F T f hsize hF hcommon wt hw herr
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYT hdiv hchange hinter hmem hbudget
  apply hNs V (by omega) L (m+1) Q F T Y hinter hmem
  intro i K _hK hdeg
  exact hσ i (Y i) (hYT i) (hdiv i) (hchange i) K (fun v=>(hdeg v).trans (hbudget i))

end Oberwolfach
