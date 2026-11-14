module

public import Oberwolfach.AvailableCommonHubFactors

@[expose] public section
/-! The bounded factor pair may use the prescribed roots while all new
vertices avoid the old vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_spoke_hub_factors (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1) (s:ℕ) (hdivs:(m+1)∣s):
    ∃ ξ:ℝ,0<ξ ∧ ∃ k:ℕ,(m+1)∣k ∧ ∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card V→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (H:V→U→Prop) (u u':U) (W T:Finset V),
    (∀ v∈T,H v u∧H v u')→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξ*Fintype.card V→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u')).card:ℝ)≤ξ*Fintype.card V→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,(∀ v∈S∪T,H v u∧H v u') ∧ S.card=k ∧ Disjoint S W ∧ Disjoint S T ∧
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
  obtain ⟨ξ,hξ,k,hk,hbase⟩:=regular_host_available_common_hub_factors m hm α hα hα1 s hdivs
  refine ⟨ξ,hξ,k,hk,?_⟩
  intro L f hL
  obtain ⟨N,hN⟩:=hbase L f hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn G F F₀ D hreg hF₀ hF H u u' W T hTH hT hTfree h₁ h₂ hW hθ
  let A₁:Finset V:=Finset.univ.filter (fun v=>H v u)
  let A₂:Finset V:=Finset.univ.filter (fun v=>H v u')
  have hTA:T⊆A₁∩A₂:=by
    intro v hv
    have hh:=hTH v hv
    simp only [A₁,A₂,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hh
  have h₁':((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V:=by
    have hh:Finset.univ\A₁=(Finset.univ:Finset V).filter (fun v=>¬H v u):=by ext v;simp [A₁]
    rw [hh];exact h₁
  have h₂':((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V:=by
    have hh:Finset.univ\A₂=(Finset.univ:Finset V).filter (fun v=>¬H v u'):=by ext v;simp [A₂]
    rw [hh];exact h₂
  obtain ⟨S,hSA,hSc,hSW,hST,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,havoid₁,havoid₂⟩:=
    hN V hn G F F₀ D hreg hF₀ hF A₁ A₂ W T hTA hT hTfree h₁' h₂' hW hθ
  refine ⟨S,?_,hSc,hSW,hST,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,havoid₁,havoid₂⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hvS|hvT
  · have hh:=hSA hvS
    simpa only [A₁,A₂,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  · exact hTH v hvT
end Oberwolfach
