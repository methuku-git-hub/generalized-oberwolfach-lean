module

public import Oberwolfach.SupportedBernoulliFactor
public import Oberwolfach.RepresentedForbiddenGraph

@[expose] public section

/-! Physical forbidden-edge avoidance after fresh sampling, including
successor representations. Both representations are required to be injective;
no permutation or graph on a restricted domain is substituted for the parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T:Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem supported_bernoulli_physical_factor (a:I→ℕ) (c J:ℕ) (hc:3≤c)
    (ha:∀ i,1≤a i) (hs:∑ i,a i=c) (S:T→VertexAbsorberTemplate c)
    (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:I→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      N≤Fintype.card (Σ i,V i)→∀ (e:(Σ i,V i)↪W) (R:C→Finset W) (w:C→ℝ),
      (∀ C₀,∀ v∈R C₀,∃ z,e z=v)→
      (∀ C₀ i,(Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈R C₀)).card=a i)→
      (∀ U:Finset W,Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(Fintype.card (Σ i,V i):ℝ)^(c-1)≤w C₀ ∧
        w C₀≤B/(Fintype.card (Σ i,V i):ℝ)^(c-1))→
      (∀ v,|1-hypergraphWeightedDegree R w (e v)|≤η)→
      (∀ ρ:∀ i,FixedSubset (V i) (a i),
        α*(Fintype.card (Σ i,V i):ℝ)^(c*c)≤
          Fintype.card (LabelledAbsorberFamily R S ((profileRootSet ρ).image e)))→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
        (FiniteLaw.pi (fun _:W=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
            (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
            (((bernoulliVertexSet (fun z=>σ (e z))\Y).card+
              (Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (Σ i,V i))→
            ∀ (P:Type) [Fintype P] [DecidableEq P] (f g:W↪P) (F:SimpleGraph P),
            (∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
            ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y.image e) ∧
              ∀ C₀∈D,∀ x∈R C₀,∀ y∈R C₀,x≠y→
                ¬F.Adj (f x) (f y) ∧ ¬F.Adj (f x) (g y) ∧
                ¬F.Adj (g x) (f y) ∧ ¬F.Adj (g x) (g y)) :=by
  obtain ⟨η,δ,hη,hδ,hbase⟩:=supported_bernoulli_graph_avoiding_factor a c J hc ha hs S α b B hα hb hB
  refine ⟨η,δ/4,hη,by positivity,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ W C _ _ _ _ hn e R w hsupp hR hJ hw herr habs
  have hevent:=hN V W C hn e R w hsupp hR hJ hw herr habs
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y k hY hchange P _ _ f g F hF
  have hs0:0≤p*(Fintype.card (Σ i,V i):ℝ):=by positivity
  have hd:δ/4≤δ:=by linarith
  have hchange':(((bernoulliVertexSet (fun z=>σ (e z))\Y).card+
      (Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤δ*(p*Fintype.card (Σ i,V i)):=
    hchange.trans (mul_le_mul_of_nonneg_right hd hs0)
  have hdeg (v:W):((representedForbiddenGraph F f g).degree v:ℝ)≤δ*(p*Fintype.card (Σ i,V i)):=by
    have hh:=representedForbiddenGraph_degree_bound F f g ((δ/4)*(p*Fintype.card (Σ i,V i))) hF v
    convert hh using 1 <;> ring
  obtain ⟨D,hD,havoid⟩:=hσ Y k hY hchange' (representedForbiddenGraph F f g) hdeg
  exact ⟨D,hD,fun C₀ hC x hx y hy hxy=>representedForbiddenGraph_avoidance F f g (R C₀)
    (havoid C₀ hC) hx hy hxy⟩

end Oberwolfach
