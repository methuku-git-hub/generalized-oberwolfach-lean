module

public import Oberwolfach.BernoulliProfileFactor
public import Oberwolfach.ForbiddenGraphPairs

@[expose] public section

/-! The fresh factor theorem with a genuine forbidden graph. The graph
and altered vertex set may be chosen after the one Bernoulli outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T:Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem bernoulli_graph_avoiding_factor (a:I→ℕ) (c J:ℕ) (hc:3≤c)
    (ha:∀ i,1≤a i) (hs:∑ i,a i=c) (S:T→VertexAbsorberTemplate c)
    (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:I→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C:Type) [Fintype C] [DecidableEq C],
      N≤Fintype.card (Σ i,V i)→∀ (R:C→Finset (Σ i,V i)) (w:C→ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈R C₀)).card=a i)→
      (∀ U:Finset (Σ i,V i),Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(Fintype.card (Σ i,V i):ℝ)^(c-1)≤w C₀ ∧
        w C₀≤B/(Fintype.card (Σ i,V i):ℝ)^(c-1))→
      (∀ v,|1-hypergraphWeightedDegree R w v|≤η)→
      (∀ ρ:∀ i,FixedSubset (V i) (a i),
        α*(Fintype.card (Σ i,V i):ℝ)^(c*c)≤Fintype.card (LabelledAbsorberFamily R S (profileRootSet ρ)))→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
        (FiniteLaw.pi (fun _:Σ i,V i=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
            (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
            (((bernoulliVertexSet σ\Y).card+(Y\bernoulliVertexSet σ).card:ℕ):ℝ)≤
              ζ*(p*Fintype.card (Σ i,V i))→
            ∀ F:SimpleGraph (Σ i,V i),
            (∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
            ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y) ∧
              ∀ C₀∈D,∀ x∈R C₀,∀ y∈R C₀,¬F.Adj x y):=by
  obtain ⟨η,δ,hη,hδ,hbase⟩:=bernoulli_profile_factor_common_event a c J hc ha hs S α b B hα hb hB
  let ζ:=min (1/4:ℝ) (δ/4)
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζ4:ζ≤1/4:=min_le_left _ _
  have hζδ:ζ≤δ/4:=min_le_right _ _
  have hζδ':ζ≤δ:=by linarith
  have h2ζ:2*ζ≤δ:=by linarith
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ C _ _ hn R w hR hJ hw herr habs
  have hevent:=hN V C hn R w hR hJ hw herr habs
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y k hY hchange F hF
  let s:ℝ:=p*Fintype.card (Σ i,V i)
  have hs0:0≤s:=by dsimp [s];positivity
  let A:=bernoulliVertexSet σ
  have hAc:(A.card:ℝ)≤s+s/4:=by
    have hh:|(A.card:ℝ)-s|≤s/4:=hσ.1
    have hh' :=(abs_le.mp hh).2
    linarith only [hh']
  have hYc:(Y.card:ℝ)≤2*s:=by
    have hy:(Y.card:ℝ)≤(A.card:ℝ)+(Y\A).card:=by
      exact_mod_cast (show Y.card≤A.card+(Y\A).card by
        simpa only [Nat.add_comm] using (Finset.card_le_card_sdiff_add_card (s:=Y) (t:=A)))
    have hd:((Y\A).card:ℝ)≤((A\Y).card+(Y\A).card:ℕ):=by
      exact_mod_cast Nat.le_add_left (Y\A).card (A\Y).card
    have hz:=mul_le_mul_of_nonneg_right hζ4 hs0
    linarith only [hy,hd,hchange,hAc,hz]
  let E:=forbiddenGraphPairs F Y
  have hd:(((A\Y).card+(Y\A).card:ℕ):ℝ)≤δ*s:=
    hchange.trans (mul_le_mul_of_nonneg_right hζδ' hs0)
  have hEs:(E.card:ℝ)≤δ*s^2:=by
    have hh:=forbiddenGraphPairs_card F Y (ζ*s) hF
    have ht:=mul_le_mul_of_nonneg_right hYc (mul_nonneg hζ.le hs0)
    have hz:=mul_le_mul_of_nonneg_right h2ζ (sq_nonneg s)
    nlinarith only [hh,ht,hz]
  have hEd (v:Σ i,V i):((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤δ*s:=by
    have hh:((E.filter (fun e=>v=e.1 ∨ v=e.2)).card:ℝ)≤2*(F.degree v:ℝ):=by
      exact_mod_cast forbiddenGraphPairs_incidence F Y v
    have hz:=mul_le_mul_of_nonneg_right h2ζ hs0
    nlinarith only [hh,hF v,hz]
  obtain ⟨D,hD,havoid⟩:=hσ.2 Y k hY hd E (forbiddenGraphPairs_distinct F Y) hEs hEd
  refine ⟨D,hD,?_⟩
  intro C₀ hC
  have hsub:R C₀⊆Y:=by
    rw [←hD.2]
    exact Finset.subset_biUnion_of_mem R hC
  exact forbiddenGraphPairs_avoidance F Y (R C₀) hsub (havoid C₀ hC)

end Oberwolfach
