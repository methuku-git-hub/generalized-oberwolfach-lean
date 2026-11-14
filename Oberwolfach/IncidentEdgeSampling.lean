module

public import Oberwolfach.SingleClassBernoulliFactor
public import Oberwolfach.EdgeRetention
public import Oberwolfach.ColourDegrees
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! A fresh boundary neighbourhood has exactly the independent vertex
law used by the factor theorem. Distinct neighbours use distinct physical
edges; this is a projection of the original edge experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem incident_edge_retention_event (z:V) (p:ℝ) (hp:0≤p) (hp1:p≤1) (A:(V→Bool)→Prop):
    (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>A (fun v=>σ s(z,v)))=
    (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability A:=by
  exact finiteLaw_pi_injective_projection_event (fun _:Sym2 V=>FiniteLaw.retentionCoin p hp hp1) (fun v=>s(z,v)) (incidentPair_injective z) A

theorem retained_neighbourhood_bernoulli (G:SimpleGraph V) (T:Finset V) (z:V)
    (hT:T⊆G.neighborFinset z) (σ:Sym2 V→Bool):
    T∩(retainedGraph G σ).neighborFinset z=T∩bernoulliVertexSet (fun v=>σ s(z,v)):=by
  ext v
  simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,retainedGraph,bernoulliVertexSet,
    Finset.mem_filter,Finset.mem_univ,true_and]
  have hh:v∈T→G.Adj z v:=fun hv=>(SimpleGraph.mem_neighborFinset _ _ _).mp (hT hv)
  tauto

end Oberwolfach
