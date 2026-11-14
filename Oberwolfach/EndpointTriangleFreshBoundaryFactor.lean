module

public import Oberwolfach.EndpointTriangleFreshFactor
public import Oberwolfach.IncidentEdgeSampling

@[expose] public section
/-! Endpoint-triangle factors in the actual independently retained physical
boundary neighbourhood of a fixed outer root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_fresh_boundary_factor (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
      ∀(A:Type) [Fintype A] [DecidableEq A],N≤Fintype.card A→
      ∀(G Q F:SimpleGraph A) (z:A) (S T:Finset A),Disjoint S T→S∪T⊆G.neighborFinset z→
      (∀v,(F.degree v:ℝ)≤ε*Fintype.card A)→
      EndpointNeighbourCounts Q F S T (γ*Fintype.card A)→
      ∀wt:EndpointTriangle Q F S T→ℝ,
      (∀C,b/(Fintype.card A:ℝ)^2≤wt C ∧ wt C≤B/(Fintype.card A:ℝ)^2)→
      (∀v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η)→
      1-1/(T.card:ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 A=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀Y:Finset A,Y⊆S∪T→(Y∩S).card=2*(Y∩T).card→
            (((((S∪T)∩(retainedGraph G σ).neighborFinset z)\Y).card+
              (Y\((S∪T)∩(retainedGraph G σ).neighborFinset z)).card:ℕ):ℝ)≤ζ*(p*T.card)→
            ∀K:SimpleGraph A,(∀v,(K.degree v:ℝ)≤ζ*(p*T.card))→
            ∃D:Finset (EndpointTriangle Q F S T),
              ((∀C∈D,∀E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
                D.biUnion endpointTriangleVertices=Y) ∧
              ∀C∈D,∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬K.Adj x y):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=endpoint_triangle_fresh_factor γ b B hγ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro A _ _ hn G Q F z S T hST hTG hF hcounts wt hw herr
  have hevent:=hN A hn Q F S T hST hF hcounts wt hw herr
  rw [←incident_edge_retention_event z p hp.le hp1] at hevent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYU hratio hchange K hK
  rw [retained_neighbourhood_bernoulli G (S∪T) z hTG σ] at hchange
  exact hσ Y hYU hratio hchange K hK
end Oberwolfach
