module

public import Oberwolfach.RootAllowedDomain
public import Oberwolfach.UniformForbiddenRootedFactors

@[expose] public section
/-! The bounded factor pair may use the prescribed roots while all new
vertices avoid the old vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_available_common_hub_factors_uniform (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ s:ℕ,(m+1)∣s→∃ k:ℕ,(m+1)∣k ∧ ∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (A₁ A₂ W T:Finset V),
    T⊆A₁∩A₂→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    ((Finset.univ\A₁).card:ℝ)≤ξ*Fintype.card V→
    ((Finset.univ\A₂).card:ℝ)≤ξ*Fintype.card V→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,S⊆A₁∩A₂ ∧ S.card=k ∧ Disjoint S W ∧ Disjoint S T ∧
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
  obtain ⟨ξ₀,hξ₀,hbase⟩:=regular_host_common_neighborhood_uniform_forbidden_factors m hm α hα hα1
  let ξ:=min ξ₀ (1/12:ℝ)
  have hξ:0<ξ:=lt_min hξ₀ (by norm_num)
  have hξ₀':ξ≤ξ₀:=min_le_left _ _
  have hξ12:ξ≤1/12:=min_le_right _ _
  refine ⟨ξ,hξ,?_⟩
  intro s hdivs
  obtain ⟨k,hk,hbase⟩:=hbase s hdivs
  refine ⟨k,hk,?_⟩
  intro L f hL
  obtain ⟨N,hN⟩:=hbase L f hL
  refine ⟨2*N,?_⟩
  intro V _ _ hn G F F₀ D hreg hF₀ hF A₁ A₂ W T hTA hT hTfree h₁ h₂ hW hθ
  let C:=W\T
  let B:=(A₁∩A₂)\C
  have hTB:T⊆B:=by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨hTA hx,fun hh=>(Finset.mem_sdiff.mp hh).2 hx⟩
  have hC:((C.card):ℝ)≤ξ*(Fintype.card V:ℝ):=by
    have hh:(C.card:ℝ)≤W.card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s:=W) (t:=T))
    exact hh.trans hW
  have hmiss:Finset.univ\B⊆((Finset.univ\A₁)∪(Finset.univ\A₂))∪C:=by
    intro x hx
    have hxB:x∉B:=(Finset.mem_sdiff.mp hx).2
    by_cases hxC:x∈C
    · exact Finset.mem_union_right _ hxC
    · apply Finset.mem_union_left
      by_cases hx₁:x∈A₁
      · apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro hx₂
        exact hxB (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hx₁,hx₂⟩,hxC⟩)
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx₁⟩)
  have hmisscard:((Finset.univ\B).card:ℝ)≤3*ξ*Fintype.card V:=by
    have hh:=(Finset.card_le_card hmiss).trans (Finset.card_union_le _ _)
    have hh':=Finset.card_union_le (Finset.univ\A₁) (Finset.univ\A₂)
    have hhR:((Finset.univ\B).card:ℝ)≤(Finset.univ\A₁).card+(Finset.univ\A₂).card+C.card:=by
      exact_mod_cast (show (Finset.univ\B).card≤(Finset.univ\A₁).card+(Finset.univ\A₂).card+C.card by omega)
    linarith
  have hBcard:B.card≤Fintype.card V:=Finset.card_le_univ B
  have hmissing:((Finset.univ\B).card:ℝ)=(Fintype.card V:ℝ)-B.card:=by
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Nat.cast_sub hBcard]
  have hnR:(2:ℝ)*N≤Fintype.card V:=by exact_mod_cast hn
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hξn:=mul_le_mul_of_nonneg_right hξ12 hn0
  have hBN:N≤B.card:=by
    have hh:(N:ℝ)≤B.card:=by nlinarith
    exact_mod_cast hh
  have hξscale:=mul_le_mul_of_nonneg_right hξ₀' hn0
  have h₁':((Finset.univ\A₁).card:ℝ)≤ξ₀*Fintype.card V:=h₁.trans hξscale
  have h₂':((Finset.univ\A₂).card:ℝ)≤ξ₀*Fintype.card V:=h₂.trans hξscale
  have hC':(C.card:ℝ)≤ξ₀*Fintype.card V:=hC.trans hξscale
  obtain ⟨S,hSsub,hSc,hST,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,havoid₁,havoid₂⟩:=
    hN V G F F₀ D hreg hF₀ hF A₁ A₂ C T hBN hTB hT hTfree h₁' h₂' hC' hθ
  have hSW:Disjoint S W:=by
    apply Finset.disjoint_left.mpr
    intro x hxS hxW
    have hxnot:x∉C:=(Finset.mem_sdiff.mp (hSsub hxS)).2
    by_cases hxT:x∈T
    · exact (Finset.disjoint_left.mp hST) hxS hxT
    · exact hxnot (Finset.mem_sdiff.mpr ⟨hxW,hxT⟩)
  refine ⟨S,?_,hSc,hSW,hST,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,havoid₁,havoid₂⟩
  exact fun x hx=>(Finset.mem_sdiff.mp (hSsub hx)).1
end Oberwolfach
