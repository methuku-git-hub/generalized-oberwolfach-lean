module

public import Oberwolfach.EndpointTriangleNormalizedEventLift
public import Oberwolfach.EndpointTriangleInnerScaleTransport

@[expose] public section
/-! Robust endpoint factors on a fixed inner physical domain, lifted to the
ambient graph on the very same sampling coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_inner_factor_probability
    (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(V W J E:Type) [Fintype V] [Fintype W] [Fintype J] [Fintype E]
      [DecidableEq V] [DecidableEq W] [DecidableEq J] [DecidableEq E]
      (e:W↪V) (Q F:SimpleGraph V) (S T:J→Finset V) (g:J→V↪E) (a:ℝ),
    N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    0<a→a≤Fintype.card W→(Fintype.card W:ℝ)≤2*a→
    (∀j v,v∈S j→∃w,e w=v)→(∀j v,v∈T j→∃w,e w=v)→
    (∀j,Disjoint (S j) (T j))→
    (∀v,(F.degree v:ℝ)≤ε*Fintype.card W)→
    (∀j,EndpointNeighbourCounts Q F (S j) (T j) (γ*Fintype.card W))→
    (∀j,∃wt:EndpointTriangle Q F (S j) (T j)→ℝ,
      (∀C,b/a^2≤wt C ∧ wt C≤B/a^2) ∧
      (∀v∈S j∪T j,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η))→
    1-1/(Fintype.card W:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (EndpointTriangleNormalizedFactorEvent Q F S T g p ζ):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=
    endpoint_triangle_normalized_factor_family γ γ b (B*2^2) hγ hγ hb (by positivity)
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V W J E _ _ _ _ _ _ _ _ e Q F S T g a hn hJ ha han hsize hS hT hdis hF hcounts hweight
  let Si:=fun j=>embeddingPullFinset e (S j)
  let Ti:=fun j=>embeddingPullFinset e (T j)
  have hdisi:∀j,Disjoint (Si j) (Ti j):=by
    intro j
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact (Finset.disjoint_left.mp (hdis j)) ((embeddingPullFinset_mem e (S j) w).mp hw)
      ((embeddingPullFinset_mem e (T j) w).mp hw')
  have hcountsi:∀j,EndpointNeighbourCounts (Q.comap e) (F.comap e) (Si j) (Ti j)
      (γ*Fintype.card W):=by
    intro j
    exact endpoint_counts_embedding e Q F (S j) (T j) (hS j) (hT j) _ (hcounts j)
  have hsizei:∀j,γ*Fintype.card W≤((Ti j).card:ℝ):=fun j=>(hcountsi j).indices
  have hFi:∀w,((F.comap e).degree w:ℝ)≤ε*Fintype.card W:=by
    intro w
    have hh:((F.comap e).degree w:ℝ)≤F.degree (e w):=by exact_mod_cast embedding_comap_degree_le e F w
    exact hh.trans (hF (e w))
  have hwi:∀j,∃wi:EndpointTriangle (Q.comap e) (F.comap e) (Si j) (Ti j)→ℝ,
      (∀C,b/(Fintype.card W:ℝ)^2≤wi C ∧ wi C≤(B*2^2)/(Fintype.card W:ℝ)^2) ∧
      (∀v∈Si j∪Ti j,|1-hypergraphWeightedDegree endpointTriangleVertices wi v|≤η):=by
    intro j
    obtain ⟨wt,hw,hl⟩:=hweight j
    exact endpoint_triangle_inner_scale_transport e Q F (S j) (T j) (hS j) (hT j)
      a b B 2 η ha han (by norm_num) hsize hb.le hB wt hw hl
  choose wi hwi hl using hwi
  have hprob:=hN W J E hn hJ (Q.comap e) (F.comap e) Si Ti (fun j=>e.trans (g j))
    hdisi hsizei hFi hcountsi wi hwi hl
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact endpoint_triangle_normalized_event_lift e Q F S T g hS hT p ζ σ hσ
end Oberwolfach
