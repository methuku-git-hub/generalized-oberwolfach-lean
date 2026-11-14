module

public import Oberwolfach.IndependentNeighbourhoodRetention

@[expose] public section
/-! One independent physical-edge reserve controls all one-root degrees
into any fixed family of counting domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_degree_domains_common_event (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀(G:SimpleGraph V) (s:ℕ),s≤Fintype.card V→∀(A:Fin s→Finset V)
      (τ:ℝ) (hτ:0≤τ) (hτ1:τ≤1),
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.retentionCoin τ hτ hτ1)).probability
        (fun σ=>∀i v,|((A i∩(retainedGraph G σ).neighborFinset v).card:ℝ)-
          τ*(A i∩G.neighborFinset v).card|<ε*Fintype.card V):=by
  obtain ⟨N,hN⟩:=retained_common_neighbourhoods_common_event 1 q ε hε
  refine ⟨N,?_⟩
  intro V _ _ hn G s hs A τ hτ hτ1
  have hh:=hN V hn G s hs A τ hτ hτ1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ i v
  have ht:=hσ i {v} (by simp)
  have he (f:V→Finset V):common (A i) {v} f=A i∩f v:=by
    ext w;simp [common,Finset.mem_inter]
  rw [he,he] at ht
  simpa only [Finset.card_singleton,pow_one] using ht
end Oberwolfach
