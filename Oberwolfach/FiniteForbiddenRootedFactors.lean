module

public import Oberwolfach.FiniteForbiddenRimDegrees
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

theorem regular_host_common_neighborhood_finite_forbidden_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ ξ:ℝ,0<ξ ∧ ∃ k:ℕ,(m+1)∣k ∧ ∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G F F₀:SimpleGraph V) (D:ℕ),
    G.IsRegularOfDegree D→(F₀.edgeFinset.card≤f)→(∀ v,(F.degree v:ℝ)≤L)→
    ∀ (A₁ A₂ C T:Finset V),let B:=(A₁∩A₂)\C;
    N≤B.card→T⊆B→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V→
    ((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V→
    (C.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,S⊆B ∧ S.card=k ∧ Disjoint S T ∧
      (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle (G\F₀) (m+1)),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices (G\F₀) (m+1) C) (ordinaryCycleVertices (G\F₀) (m+1) E)) ∧
        M₁.biUnion (ordinaryCycleVertices (G\F₀) (m+1))=S∪T ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices (G\F₀) (m+1) C) (ordinaryCycleVertices (G\F₀) (m+1) E)) ∧
        M₂.biUnion (ordinaryCycleVertices (G\F₀) (m+1))=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices (G\F₀) (m+1) C∩T).card≤1) ∧
        (∀ C∈M₁,Disjoint C.val.val.edgeFinset F₀.edgeFinset) ∧
        (∀ C∈M₂,Disjoint C.val.val.edgeFinset F₀.edgeFinset):=by
  obtain ⟨ξ,hξ,k,hk,hbase⟩:=regular_subgraph_common_neighborhood_physical_factors m hm α hα hα1 s hdivs
  refine ⟨ξ,hξ,k,hk,?_⟩
  intro L f hL
  obtain ⟨N,hN⟩:=hbase L f hL (by positivity)
  refine ⟨N,?_⟩
  intro V _ _ G F F₀ D hreg hF₀ hF A₁ A₂ C T B hB hTB hT hTfree h₁ h₂ hC hθ
  let Q:SimpleGraph V:=G\F₀
  letI : DecidableRel Q.Adj := fun _ _ => Classical.propDecidable _
  have hQ:Q≤G:=fun _ _ h=>h.1
  have hdel:=finite_forbidden_rim_deletion_degree_of_eq G Q F₀ rfl f hF₀
  obtain ⟨S,hSsub,hSc,hdis,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot⟩:=
    hN V G Q F D hreg hQ hdel hF A₁ A₂ C T hB hTB hT hTfree h₁ h₂ hC hθ
  refine ⟨S,hSsub,hSc,hdis,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,?_,?_⟩
  · intro C hC;exact cycle_in_forbidden_rim_complement G F₀ (m+1) C
  · intro C hC;exact cycle_in_forbidden_rim_complement G F₀ (m+1) C
end Oberwolfach
