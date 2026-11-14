module

public import Oberwolfach.BoundaryReserveDegreeEvent

@[expose] public section
/-! The same independent-edge reserve has controlled total physical degree
at every vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_graph_degrees_common_event (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀(G:SimpleGraph V) (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (fun σ=>∀v,|((retainedGraph G σ).degree v:ℝ)-τ*G.degree v|<ε*Fintype.card V):=by
  obtain ⟨N,hN⟩:=retained_degree_domains_common_event q ε hε
  refine ⟨max 1 N,?_⟩
  intro V _ _ hn G τ hτ hτ1
  have h:=hN V (by omega) G 1 (by omega) (fun _=>Finset.univ) τ hτ hτ1
  apply h.trans
  apply finiteLaw_probability_mono
  intro σ hs v
  have hv:=hs 0 v
  simpa only [Finset.univ_inter,SimpleGraph.card_neighborFinset_eq_degree] using hv
end Oberwolfach
