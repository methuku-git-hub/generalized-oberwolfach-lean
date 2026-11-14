module

public import Oberwolfach.OrdinaryHubTradeCertificate
public import Oberwolfach.UniformRootBoundHubTrade
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section
/-! Choose a bounded family of hub switches one at a time. The new row
sets and root sets are pairwise disjoint and all switches use the original
physical host and forbidden-edge set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_indexed_hub_trades_uniform (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ q p:ℕ,∃ t:ℕ,∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V U I:Type) [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U] [DecidableEq I],N≤Fintype.card V→Fintype.card I≤p→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (H:V→U→Prop) (u u':I→U) (W:Finset V)
      (T:I→Finset V) (z:I→ℕ),
    (∀ i,u i≠u' i)→(∀ i,z i≤q)→(∀ i,(T i).card=(m+1)*z i)→
    (∀ i,T i⊆W)→(∀ i j,i≠j→Disjoint (T i) (T j))→
    (∀ i,∀ v∈T i,H v (u i)∧H v (u' i))→
    (∀ i,∀ x∈T i,∀ y∈T i,¬F.Adj x y)→
    (∀ i,(((Finset.univ:Finset V).filter (fun v=>¬H v (u i))).card:ℝ)≤ξ*Fintype.card V)→
    (∀ i,(((Finset.univ:Finset V).filter (fun v=>¬H v (u' i))).card:ℝ)≤ξ*Fintype.card V)→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:I→Finset V,
      (∀ i,(S i).card≤t ∧ Disjoint (S i) W ∧ Disjoint (S i) (T i) ∧
        (∀ v∈S i∪T i,H v (u i)∧H v (u' i)) ∧
        (∀ x∈S i∪T i,∀ y∈S i∪T i,¬F.Adj x y) ∧
        OrdinaryHubTradeCertificate (G\F₀) F H (u i) (u' i) (S i) (T i) (m+1)) ∧
      (∀ i j,i≠j→Disjoint (S i∪T i) (S j∪T j)) ∧
      (∀ i j,i≠j→∀ x∈S i,∀ y∈S j,¬F.Adj x y):=by
  obtain ⟨ξ₀,hξ₀,hbase⟩:=regular_host_spoke_hub_trade_uniform_root_bound m hm α hα hα1
  refine ⟨ξ₀/2,by positivity,?_⟩
  intro q p
  obtain ⟨t,hbase⟩:=hbase q
  refine ⟨t,?_⟩
  intro L f hL
  obtain ⟨N₀,hN₀⟩:=hbase L f hL
  obtain ⟨N₁,hN₁⟩:=eventually_constant_le_linear ((p:ℝ)*t*(L+1)) (ξ₀/2) (by positivity)
  refine ⟨max N₀ N₁,?_⟩
  intro V U I _ _ _ _ _ _ hn hI G F F₀ D hreg hF₀ hF H u u' W T z hune hz hT hTW hTT hTH hTfree h₁ h₂ hW hθ
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hbudget:(p:ℝ)*t*(L+1)≤(ξ₀/2)*Fintype.card V:=hN₁ _ (by omega)
  have h₁' (i:I):(((Finset.univ:Finset V).filter (fun v=>¬H v (u i))).card:ℝ)≤ξ₀*Fintype.card V:=by
    have hh:=h₁ i
    nlinarith
  have h₂' (i:I):(((Finset.univ:Finset V).filter (fun v=>¬H v (u' i))).card:ℝ)≤ξ₀*Fintype.card V:=by
    have hh:=h₂ i
    nlinarith
  let Good:I→Finset V→Prop:=fun i S=>Disjoint S W ∧ Disjoint S (T i) ∧
    (∀ v∈S∪T i,H v (u i)∧H v (u' i)) ∧
    (∀ x∈S∪T i,∀ y∈S∪T i,¬F.Adj x y) ∧
    OrdinaryHubTradeCertificate (G\F₀) F H (u i) (u' i) S (T i) (m+1)
  have hchoose:∀ i:I,∀ B:Finset V,
      (B.card:ℝ)≤(∅:Finset V).card+Fintype.card (I)*t*(L+1)→
      ∃ S,Good i S ∧ S.card≤t ∧ Disjoint S B:=by
    intro i B hB
    let W':=W∪B
    have hW'R:(W'.card:ℝ)≤W.card+B.card:=by exact_mod_cast Finset.card_union_le W B
    have hB':(B.card:ℝ)≤(p:ℝ)*t*(L+1):=by
      have hIr:(Fintype.card I:ℝ)≤p:=by exact_mod_cast hI
      have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIr (by positivity:0≤(t:ℝ))) (by linarith:0≤L+1)
      simp only [Finset.card_empty,Nat.cast_zero,zero_add] at hB
      exact hB.trans hh
    have hW'budget:(W'.card:ℝ)≤ξ₀*Fintype.card V:=by linarith
    obtain ⟨S,hSH,hSc,hSW,hST,hfree,R,hplus,hminus,hp,hm',hR,hsupp,hno,hSp,hSm,hid⟩:=
      hN₀ V U (by omega) G F F₀ D hreg hF₀ hF H (u i) (u' i) (hune i) W' (T i) (z i) (hz i)
        (hTH i) (hT i) (hTfree i) (h₁' i) (h₂' i) hW'budget hθ
    exact ⟨S,⟨hSW.mono_right Finset.subset_union_left,hST,hSH,hfree,R,hplus,hminus,hp,hm',hR,hsupp,hno,hSp,hSm,hid⟩,
      hSc,hSW.mono_right Finset.subset_union_right⟩
  obtain ⟨S,hS,hsep⟩:=finite_conflict_separated_choices (fun S:Finset V=>S) Good ∅ t F L hL hF hchoose
  refine ⟨S,?_,?_,?_⟩
  · intro i
    exact ⟨(hS i).2.1,(hS i).1.1,(hS i).1.2.1,(hS i).1.2.2.1,(hS i).1.2.2.2.1,(hS i).1.2.2.2.2⟩
  · intro i j hij
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_union_right.mpr
      exact ⟨(hsep i j hij).1,(hS i).1.1.mono_right (hTW j)⟩
    · apply Finset.disjoint_union_right.mpr
      exact ⟨((hS j).1.1.mono_right (hTW i)).symm,hTT i j hij⟩
  · intro i j hij
    exact (hsep i j hij).2
end Oberwolfach
