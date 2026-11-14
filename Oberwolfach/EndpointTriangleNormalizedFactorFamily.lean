module

public import Oberwolfach.EndpointTriangleFreshFactor
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FixedDomainQuadraticEvent

@[expose] public section
/-! Simultaneous endpoint-triangle factors on the actual inner physical
vertex type, using the same ambient independent sampling coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def EndpointTriangleNormalizedFactorEvent
    {W J E:Type} [Fintype W] [Fintype J] [Fintype E] [DecidableEq W] [DecidableEq J]
    (Q F:SimpleGraph W) (S T:J→Finset W) (f:J→W↪E) (p ζ:ℝ) (σ:E→Bool):Prop :=
  ∀j,∀Y:Finset W,Y⊆S j∪T j→(Y∩S j).card=2*(Y∩T j).card→
    (((((S j∪T j)∩bernoulliVertexSet (fun w=>σ (f j w)))\Y).card+
      (Y\((S j∪T j)∩bernoulliVertexSet (fun w=>σ (f j w)))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
    ∀K:SimpleGraph W,(∀v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
    ∃D:Finset (EndpointTriangle Q F (S j) (T j)),
      ((∀C∈D,∀C'∈D,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
      D.biUnion endpointTriangleVertices=Y) ∧
      ∀C∈D,∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬K.Adj x y

theorem endpoint_triangle_normalized_factor_family
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀(p:ℝ) (hp:0<p) (hp1:p≤1),∀q:ℕ,∃N:ℕ,
    ∀(W J E:Type) [Fintype W] [Fintype J] [Fintype E] [DecidableEq W] [DecidableEq J] [DecidableEq E],
      N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    ∀(Q F:SimpleGraph W) (S T:J→Finset W) (f:J→W↪E),
      (∀j,Disjoint (S j) (T j))→(∀j,κ*Fintype.card W≤((T j).card:ℝ))→
      (∀v,(F.degree v:ℝ)≤ε*Fintype.card W)→
      (∀j,EndpointNeighbourCounts Q F (S j) (T j) (γ*Fintype.card W))→
    ∀wt:∀j,EndpointTriangle Q F (S j) (T j)→ℝ,
      (∀j C,b/(Fintype.card W:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card W:ℝ)^2)→
      (∀j v,v∈S j∪T j→|1-hypergraphWeightedDegree endpointTriangleVertices (wt j) v|≤η)→
    1-1/(Fintype.card W:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (EndpointTriangleNormalizedFactorEvent Q F S T f p ζ):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=endpoint_triangle_fresh_factor γ b B hγ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (q+3)
  obtain ⟨Nc,hNc⟩:=fixed_domain_quadratic_common_event κ hκ q
  refine ⟨max Nf Nc,?_⟩
  intro W J E _ _ _ _ _ _ hn hJ Q F S T f hdis hsize hF hcounts wt hw hload
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)
  let Good:=fun (j:J) (σ:E→Bool)=>∀Y:Finset W,Y⊆S j∪T j→(Y∩S j).card=2*(Y∩T j).card→
    (((((S j∪T j)∩bernoulliVertexSet (fun w=>σ (f j w)))\Y).card+
      (Y\((S j∪T j)∩bernoulliVertexSet (fun w=>σ (f j w)))).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
    ∀K:SimpleGraph W,(∀v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
    ∃D:Finset (EndpointTriangle Q F (S j) (T j)),
      ((∀C∈D,∀C'∈D,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
      D.biUnion endpointTriangleVertices=Y) ∧
      ∀C∈D,∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬K.Adj x y
  have hlocal (j:J):1-1/((T j).card:ℝ)^(q+3)≤μ.probability (Good j):=by
    have hh:=hNf W (by omega) Q F (S j) (T j) (hdis j) hF (hcounts j) (wt j) (hw j) (hload j)
    have hprojection:=finiteLaw_pi_injective_projection_event
      (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1) (f j) (f j).injective
      (fun σ:W→Bool=>∀Y:Finset W,Y⊆S j∪T j→(Y∩S j).card=2*(Y∩T j).card→
        (((((S j∪T j)∩bernoulliVertexSet σ)\Y).card+
          (Y\((S j∪T j)∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*(T j).card)→
        ∀K:SimpleGraph W,(∀v,(K.degree v:ℝ)≤ζ*(p*(T j).card))→
        ∃D:Finset (EndpointTriangle Q F (S j) (T j)),
          ((∀C∈D,∀C'∈D,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
          D.biUnion endpointTriangleVertices=Y) ∧
          ∀C∈D,∀x∈endpointTriangleVertices C,∀y∈endpointTriangleVertices C,¬K.Adj x y)
    rw [←hprojection] at hh
    exact hh
  exact hNc (Fintype.card W) (by omega) (E→Bool) J hJ μ (fun j=>(T j).card) Good hsize hlocal
end Oberwolfach
