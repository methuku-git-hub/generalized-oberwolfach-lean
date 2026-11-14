module

public import Oberwolfach.CommonNeighborhoodSubgraphFactors
public import Oberwolfach.RootSeparatedFactorsAmbient

@[expose] public section
/-! Physical factor pair in a common neighbourhood after bounded-degree
edge deletions, with conflict-free vertices and at most one root per cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_subgraph_common_neighborhood_physical_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ ξ:ℝ,0<ξ ∧ ∃ k:ℕ,(m+1)∣k ∧ ∀ L t:ℝ,0≤L→0≤t→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G Q F:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→Q≤G→(∀ v,((G\Q).degree v:ℝ)≤t)→(∀ v,(F.degree v:ℝ)≤L)→
    ∀ (A₁ A₂ C T:Finset V),let B:=(A₁∩A₂)\C;
    N≤B.card→T⊆B→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V→
    ((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V→
    (C.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,S⊆B ∧ S.card=k ∧ Disjoint S T ∧
      (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle Q (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices Q (m+1) C) (ordinaryCycleVertices Q (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices Q (m+1))=S∪T ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices Q (m+1) C) (ordinaryCycleVertices Q (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices Q (m+1))=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices Q (m+1) C∩T).card≤1):=by
  obtain ⟨ξ,hξ,k,hk,hbase⟩:=regular_subgraph_common_neighborhood_conflict_free_factors m hm α hα hα1 s hdivs
  refine ⟨ξ,hξ,k,hk,?_⟩
  intro L t hL ht
  obtain ⟨N,hN⟩:=hbase L t hL ht
  refine ⟨N,?_⟩
  intro V _ _ G Q F D hreg hQ hdel hF A₁ A₂ C T B hB hTB hT hTfree h₁ h₂ hC hθ
  have hp:=hN V G Q F D hreg hQ hdel hF A₁ A₂ C T hB hTB hT hTfree h₁ h₂ hC hθ
  exact root_separated_factors_ambient Q F B T hTB (m+1) k hp
end Oberwolfach
