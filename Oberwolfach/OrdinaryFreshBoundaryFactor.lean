module

public import Oberwolfach.OrdinaryFreshLocalFactor
public import Oberwolfach.IncidentEdgeSampling

@[expose] public section

/-! Ordinary fresh factors in a boundary neighbourhood sampled by its
actual physical incident edges. No replacement sampling law is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_boundary_factor (m:ℕ) (hm:2≤m) (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
      ∀ (G Q F:SimpleGraph V) (z:V) (T:Finset V),T⊆G.neighborFinset z→κ*Fintype.card V≤(T.card:ℝ)→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ X:Finset V,X.card≤(if m=2 then 3 else 2)→
        γ*Fintype.card V≤((common T X (fun x=>Q.neighborFinset x)).card:ℝ))→
      ∀ wt:LocalOrdinaryCycle Q F T (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m)→
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)→
      1-1/(T.card:ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Finset V,Y⊆T → (m+1)∣Y.card →
            ((((T∩(retainedGraph G σ).neighborFinset z)\Y).card+(Y\(T∩(retainedGraph G σ).neighborFinset z)).card:ℕ):ℝ)≤ζ*(p*T.card)→
            ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*T.card))→
            ∃ D:Finset (LocalOrdinaryCycle Q F T (m+1)),
              ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
                D.biUnion localOrdinaryVertices=Y) ∧
              ∀ C∈D,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y) :=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_local_factor m hm γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ hn G Q F z T hTG hsize hF hcommon wt hw herr
  have hevent:=hN V hn Q F T hsize hF hcommon wt hw herr
  rw [←incident_edge_retention_event z p hp.le hp1] at hevent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYT hdiv hchange K hK
  rw [retained_neighbourhood_bernoulli G T z hTG σ] at hchange
  exact hσ Y hYT hdiv hchange K hK

end Oberwolfach
