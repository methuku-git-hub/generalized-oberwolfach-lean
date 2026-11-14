module

public import Oberwolfach.OrdinaryBoundedTwoFactors
public import Oberwolfach.OrdinaryHubFactorTrade
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Construct the bounded hub switch directly from the common cycle
weights and absorber counts. No cycle-factor existence assumption or
minimum-degree-only factor theorem is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_bounded_hub_trade (r:ℕ) (hr:3≤r)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (T:Finset V) (u u':U),u≠u'→
      (∀ v∈T,H v u∧H v u')→(T.card:ℝ)=r*k→(∀ v,(F.degree v:ℝ)≤D)→
      ∀ w:LocalOrdinaryCycle Q F T r→ℝ,
      (∀ C,b/k^(r-1)≤w C ∧ w C≤B/k^(r-1))→
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η)→
      (∀ X:Finset V,X⊆T→X.card=r→α*k^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X))→
      ∀ (I Z:Finset V) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆T→Z.card=r*z→z≤q→
      ∃ A:Finset V,∃ R:SimpleGraph V,A⊆T ∧ Disjoint A (Z∪I) ∧ A.card=r*t ∧
        (∀ x∈A,∀ y∈A,¬F.Adj x y) ∧ R≤Q ∧
        (∀ v w,R.Adj v w→v∈A∪Z∧w∈A∪Z∧(v∈A∨w∈A)) ∧
        (∀ v,R.degree v≤4) ∧
        HasOrdinaryWheelDecomposition R (fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')) r ∧
        HasOrdinaryWheelDecomposition R (fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u)) r ∧
        (∀ e:Sym2 V⊕(V×U),
          (if e∈ordinaryHostResources R (fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')) then (1:ℤ) else 0)-
          (if e∈ordinaryHostResources R (fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u)) then 1 else 0)=
          (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
          (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0)):=by
  obtain ⟨η,hη,hbase⟩:=ordinary_bounded_two_factors r hr S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ D hF₀ hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V U _ _ _ _ Q F H T u u' hu hH hT hF w hw herr habs I Z z hI hZT hZ hz
  obtain ⟨A,M₀,M₁,hAT,hAI,hAc,hAF,h₀,h₁,hdis,hcap⟩:=
    hbase k hk V Q F T hT hF w hw herr habs I Z z hI hZT hZ hz
  have hAZ:Disjoint A Z:=hAI.mono_right Finset.subset_union_left
  have hAZT:A∪Z⊆T:=Finset.union_subset hAT hZT
  obtain ⟨hplus,hminus,hRQ,_hSplus,_hSminus,hid⟩:=ordinary_hub_factor_trade (H:=H) A Z hAZ u u' hu
    M₀ M₁ h₀ h₁ hdis (fun v hv=>hH v (hAZT hv))
  let R:=localOrdinaryFactorGraph M₁⊔localOrdinaryFactorGraph M₀
  have hsupport (M:Finset (LocalOrdinaryCycle Q F T r)) (Y:Finset V)
      (hcover:M.biUnion localOrdinaryVertices=Y) (v w:V) (hvw:(localOrdinaryFactorGraph M).Adj v w):
      v∈Y∧w∈Y:=by
    obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj M v w).mp hvw
    rw [←hcover]
    exact ⟨Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_left⟩,
      Finset.mem_biUnion.mpr ⟨C,hC,Set.mem_toFinset.mpr hCvw.mem_support_right⟩⟩
  have hnoZ (v w:V) (hv:v∈Z) (hw:w∈Z):¬(localOrdinaryFactorGraph M₁).Adj v w:=by
    intro hvw
    obtain ⟨C,hC,hCvw⟩:=(localOrdinaryFactorGraph_adj M₁ v w).mp hvw
    have hpair:({v,w}:Finset V)⊆localOrdinaryVertices C∩Z:=by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl
      · exact Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr hCvw.mem_support_left,hv⟩
      · exact Finset.mem_inter.mpr ⟨Set.mem_toFinset.mpr hCvw.mem_support_right,hw⟩
    have hc2:({v,w}:Finset V).card=2:=Finset.card_pair (Q.ne_of_adj (C.val.property hCvw))
    have hc:({v,w}:Finset V).card≤1:=(Finset.card_le_card hpair).trans (hcap C hC)
    omega
  refine ⟨A,R,hAT,hAI,hAc,hAF,hRQ,?_,?_,hplus,hminus,hid⟩
  · intro v w hvw
    rcases hvw with hvw|hvw
    · have hh:=hsupport M₁ (A∪Z) h₁.2 v w hvw
      refine ⟨hh.1,hh.2,?_⟩
      by_contra hn
      have hv:v∈Z:=(Finset.mem_union.mp hh.1).resolve_left (fun h=>hn (Or.inl h))
      have hw:w∈Z:=(Finset.mem_union.mp hh.2).resolve_left (fun h=>hn (Or.inr h))
      exact hnoZ v w hv hw hvw
    · have hh:=hsupport M₀ A h₀.2 v w hvw
      exact ⟨Finset.mem_union_left _ hh.1,Finset.mem_union_left _ hh.2,Or.inl hh.1⟩
  · intro v
    have hdeg₀:=localOrdinaryFactorGraph_degree M₀ h₀.1 v
    have hdeg₁:=localOrdinaryFactorGraph_degree M₁ h₁.1 v
    have hh:=(graph_degree_sup_le (localOrdinaryFactorGraph M₁) (localOrdinaryFactorGraph M₀) v).trans
      (Nat.add_le_add hdeg₁ hdeg₀)
    simpa only [R,←SimpleGraph.ncard_neighborSet] using hh

end Oberwolfach
