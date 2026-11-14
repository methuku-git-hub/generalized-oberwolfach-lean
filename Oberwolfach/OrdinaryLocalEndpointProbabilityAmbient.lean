module

public import Oberwolfach.OrdinaryLocalEndpointProbability
public import Oberwolfach.OrdinaryEndpointGeometryInduce

@[expose] public section
/-! The local-scale endpoint probability can be applied using row and
codegree estimates stated on the ambient physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_endpoint_probability_ambient (p₀ a:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1):
    ∃η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀(b q:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),∃N:ℕ,
    ∀(W K E:Type) [Fintype W] [Fintype K] [Fintype E] [DecidableEq W] [DecidableEq K] [DecidableEq E]
      (G F:SimpleGraph W) (T:Finset W) (S R:K→Finset W) (g:K→W↪E) (t:K→ℝ),
    N≤T.card→Fintype.card K≤T.card^2→
    (∀k,S k⊆T)→(∀k,R k⊆T)→(∀k,Disjoint (S k) (R k))→
    (∀k,p₀≤t k ∧ t k≤1)→
    (∀k,a*T.card≤((S k).card:ℝ) ∧ a*T.card≤((R k).card:ℝ))→
    (∀v,F.degree v≤b)→
    (∀k v,v∈S k→|(((R k)∩G.neighborFinset v).card:ℝ)-t k*(R k).card|≤η*(R k).card)→
    (∀k v,v∈R k→|(((S k)∩G.neighborFinset v).card:ℝ)-t k*(S k).card|≤η*(S k).card)→
    (∀k v,v∈S k→∀w,w∈S k→v≠w→¬F.Adj v w→
      ((((R k)∩G.neighborFinset v)∩G.neighborFinset w).card:ℝ)≤(t k^2+η)*(R k).card)→
    1-1/(T.card:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (OrdinaryLocalEndpointEvent G F T S R g p ζ):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=ordinary_local_endpoint_probability p₀ a hp₀ hp₀1 ha ha1
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro b q p hp hp1
  obtain ⟨N,hN⟩:=hbase b q p hp hp1
  refine ⟨N,?_⟩
  intro W K E _ _ _ _ _ _ G F T S R g t hn hK hST hRT hdis ht hsize hF hrow hcol hcodeg
  have hg:=ordinary_endpoint_geometry_induce G F T S R t a η hST hRT hsize hrow hcol hcodeg
  exact hN W K E G F T S R g t hn hK hST hRT hdis ht hsize hF hg.2.1 hg.2.2.1 hg.2.2.2
end Oberwolfach
