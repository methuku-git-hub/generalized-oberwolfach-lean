module

public import Oberwolfach.SingleClassBoundedFactors
public import Oberwolfach.CanonicalGraphPairs
public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.ForbiddenGraphPairs

@[expose] public section

/-! The actual two ordinary cycle factors used in a wheel transformer.
Their bounded vertex set is chosen before the forbidden-set and conflict
bounds. Physical edge disjointness follows from canonical edge pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_bounded_two_factors (r:ℕ) (hr:3≤r)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (V:Type) [Fintype V] [DecidableEq V],
      ∀ (Q F:SimpleGraph V) (T:Finset V),(T.card:ℝ)=r*k→
      (∀ v,(F.degree v:ℝ)≤D)→
      ∀ w:LocalOrdinaryCycle Q F T r→ℝ,
      (∀ C,b/k^(r-1)≤w C ∧ w C≤B/k^(r-1))→
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices w v|≤η)→
      (∀ X:Finset V,X⊆T→X.card=r→α*k^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X))→
      ∀ (I Z:Finset V) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆T→Z.card=r*z→z≤q→
      ∃ A:Finset V,∃ D₀ D₁:Finset (LocalOrdinaryCycle Q F T r),
        A⊆T ∧ Disjoint A (Z∪I) ∧ A.card=r*t ∧
        (∀ x∈A,∀ y∈A,¬F.Adj x y) ∧
        ((∀ x∈D₀,∀ y∈D₀,x≠y→Disjoint (localOrdinaryVertices x) (localOrdinaryVertices y)) ∧
          D₀.biUnion localOrdinaryVertices=A) ∧
        ((∀ x∈D₁,∀ y∈D₁,x≠y→Disjoint (localOrdinaryVertices x) (localOrdinaryVertices y)) ∧
          D₁.biUnion localOrdinaryVertices=A∪Z) ∧
        Disjoint (localOrdinaryFactorGraph D₀) (localOrdinaryFactorGraph D₁) ∧
        ∀ C∈D₁,(localOrdinaryVertices C∩Z).card≤1:=by
  have hJ:1≤r^r:=by have hpos:0<r^r:=pow_pos (by omega) _;omega
  obtain ⟨η,hη,hbase⟩:=single_class_bounded_factors r (r^r) hr hJ S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ (r*D) hF₀ (by positivity)
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V _ _ Q F T hT hF w hw herr habs I Z z hI hZT hZ hz
  let P:LocalOrdinaryCycle Q F T r→Finset (V×V):=fun C=>canonicalGraphPairs C.val.val.val
  have hP (C:LocalOrdinaryCycle Q F T r) (p:V×V) (hp:p∈P C):
      p.1≠p.2∧p.1∈localOrdinaryVertices C∧p.2∈localOrdinaryVertices C:=by
    have he:=canonicalGraphPairs_adj C.val.val.val p hp
    exact ⟨C.val.val.val.ne_of_adj he,Set.mem_toFinset.mpr he.mem_support_left,Set.mem_toFinset.mpr he.mem_support_right⟩
  have hPc (C:LocalOrdinaryCycle Q F T r):(P C).card≤r:=by
    dsimp only [P]
    rw [canonicalGraphPairs_card,C.val.val.property.edgeFinset_card]
  have hPd (C:LocalOrdinaryCycle Q F T r) (v:V):((P C).filter (fun p=>v=p.1∨v=p.2)).card≤2:=by
    dsimp only [P]
    rw [canonicalGraphPairs_incidence]
    rcases C.val.val.property.degree_zero_or_two v with h|h <;> omega
  have hEc:((forbiddenGraphPairs F T).card:ℝ)≤(r*D)*k:=by
    apply (forbiddenGraphPairs_card F T D hF).trans
    rw [hT];ring_nf;exact le_rfl
  obtain ⟨A,D₀,D₁,hAT,hAI,hAc,hAE,hD₀,hD₁,hdis,hcap⟩:=hbase k hk V (LocalOrdinaryCycle Q F T r)
    T localOrdinaryVertices w hT (fun C v hv=>C.property.1 v (Set.mem_toFinset.mp hv))
    localOrdinaryVertices_card (local_ordinary_multiplicity Q F T) hw herr habs I Z z hI hZT hZ hz
    (forbiddenGraphPairs F T) (forbiddenGraphPairs_distinct F T) hEc P hP hPc hPd
  refine ⟨A,D₀,D₁,hAT,hAI,hAc,forbiddenGraphPairs_avoidance F T A hAT hAE,hD₀,hD₁,?_,hcap⟩
  apply disjoint_iff_inf_le.mpr
  intro v u hvu
  obtain ⟨C,hC,hCu⟩:=(localOrdinaryFactorGraph_adj D₀ v u).mp hvu.1
  obtain ⟨C',hC',hC'u⟩:=(localOrdinaryFactorGraph_adj D₁ v u).mp hvu.2
  exact (Finset.disjoint_left.mp hdis
    (Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_image.mpr ⟨s(v,u),SimpleGraph.mem_edgeFinset.mpr hCu,rfl⟩⟩)
    (Finset.mem_biUnion.mpr ⟨C',hC',Finset.mem_image.mpr ⟨s(v,u),SimpleGraph.mem_edgeFinset.mpr hC'u,rfl⟩⟩)).elim

end Oberwolfach
