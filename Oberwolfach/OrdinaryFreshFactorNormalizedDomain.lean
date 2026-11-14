module

public import Oberwolfach.OrdinaryFreshFactorInsideRootsGeneral
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! The fresh factor tolerance can be selected using the size of the actual
inner domain, independently of its proportion in a larger ambient host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_factor_normalized_domain_probability
    (m:ℕ) (hm:2≤m) (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀(p:ℝ) (hp:0<p) (hp1:p≤1),∀q:ℕ,∃N:ℕ,
    ∀(A E:Type) [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E],
      N≤Fintype.card A→∀(f:A↪E) (Q F:SimpleGraph A),
    (∀v,(F.degree v:ℝ)≤ε*Fintype.card A)→
    (∀X:Finset A,X.card≤(if m=2 then 3 else 2)→
      γ*Fintype.card A≤((common Finset.univ X (fun x=>Q.neighborFinset x)).card:ℝ))→
    ∀wt:LocalOrdinaryCycle Q F Finset.univ (m+1)→ℝ,
    (∀C,b/(Fintype.card A:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card A:ℝ)^m)→
    (∀v,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)→
    1-1/(Fintype.card A:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (fun σ=>∀Y:Finset A,(m+1)∣Y.card→
        ((((Finset.univ∩bernoulliVertexSet (fun a=>σ (f a)))\Y).card+
          (Y\(Finset.univ∩bernoulliVertexSet (fun a=>σ (f a)))).card:ℕ):ℝ)≤ζ*(p*Fintype.card A)→
        ∀K:SimpleGraph A,(∀v,(K.degree v:ℝ)≤ζ*(p*Fintype.card A))→
        ∃D:Finset (LocalOrdinaryCycle Q F Finset.univ (m+1)),
          ((∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
            D.biUnion localOrdinaryVertices=Y) ∧
          ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,hbase⟩:=ordinary_fresh_factor_inside_roots_general m hm γ 1 b B hγ (by norm_num) hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro A E _ _ _ _ hn f Q F hF hcommon wt hw hload
  let Good:=fun σ:A→Bool=>∀Y:Finset A,(m+1)∣Y.card→
    ((((Finset.univ∩bernoulliVertexSet σ)\Y).card+(Y\(Finset.univ∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*Fintype.card A)→
    ∀K:SimpleGraph A,(∀v,(K.degree v:ℝ)≤ζ*(p*Fintype.card A))→
    ∃D:Finset (LocalOrdinaryCycle Q F Finset.univ (m+1)),
      ((∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        D.biUnion localOrdinaryVertices=Y) ∧
      ∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y
  have hh:=hN A hn Q F Finset.univ (by simp) hF
    (by intro X _ hX;exact hcommon X hX) wt hw (by intro v _;exact hload v)
  have hgood:1-1/(Fintype.card A:ℝ)^q≤
      (FiniteLaw.pi (fun _:A=>FiniteLaw.retentionCoin p hp.le hp1)).probability Good:=by
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hσ Y hdiv hchange K hK
    exact hσ Y (Finset.subset_univ Y) hdiv hchange K hK
  have hprojection:=finiteLaw_pi_injective_projection_event
    (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1) f f.injective Good
  rw [←hprojection] at hgood
  exact hgood
end Oberwolfach
