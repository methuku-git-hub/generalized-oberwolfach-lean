module

public import Oberwolfach.UniformSpokeHubFactors
public import Oberwolfach.OrdinaryRootSeparatedHubTrade
public import Oberwolfach.WheelDecompositionConflictRecovery

@[expose] public section
/-! The selected separated factors yield the two actual wheel
decompositions and the exact spoke trade at a pair of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_spoke_hub_trade_uniform (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ s:ℕ,(m+1)∣s→∃ k:ℕ,(m+1)∣k ∧ ∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card V→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (H:V→U→Prop) (u u':U),u≠u'→∀ (W T:Finset V),
    (∀ v∈T,H v u∧H v u')→T.card=s→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξ*Fintype.card V→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u')).card:ℝ)≤ξ*Fintype.card V→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,(∀ v∈S∪T,H v u∧H v u') ∧ S.card=k ∧ Disjoint S W ∧ Disjoint S T ∧
      (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧ ∃ R:SimpleGraph V,
      let Sp:V→U→Prop:=fun v z=>(v∈S∪T∧z=u)∨(v∈S∧z=u')
      let Sm:V→U→Prop:=fun v z=>(v∈S∪T∧z=u')∨(v∈S∧z=u);
      HasOrdinaryWheelDecomposition R Sp (m+1) ∧ HasOrdinaryWheelDecomposition R Sm (m+1) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=G\F₀) (F:=F) (Hbase:=H) (r:=m+1)) (ordinaryHostResources R Sp) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=G\F₀) (F:=F) (Hbase:=H) (r:=m+1)) (ordinaryHostResources R Sm) ∧
      R≤G\F₀ ∧ (∀ v w,R.Adj v w→v∈S∪T∧w∈S∪T) ∧
      (∀ v w,v∈T→w∈T→¬R.Adj v w) ∧
      (∀ v z,Sp v z→H v z) ∧ (∀ v z,Sm v z→H v z) ∧
      (∀ e:Sym2 V⊕(V×U),
        (if e∈ordinaryHostResources R Sp then (1:ℤ) else 0)-
        (if e∈ordinaryHostResources R Sm then 1 else 0)=
        (if e∈T.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈T.image (fun v=>Sum.inr (v,u')) then 1 else 0)):=by
  obtain ⟨ξ,hξ,hbase⟩:=regular_host_spoke_hub_factors_uniform m hm α hα hα1
  refine ⟨ξ,hξ,?_⟩
  intro s hdivs
  obtain ⟨k,hk,hbase⟩:=hbase s hdivs
  refine ⟨k,hk,?_⟩
  intro L f hL
  obtain ⟨N,hN⟩:=hbase L f hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn G F F₀ D hreg hF₀ hF H u u' hune W T hTH hT hTfree h₁ h₂ hW hθ
  obtain ⟨S,hSH,hSc,hSW,hST,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot,havoid₁,havoid₂⟩:=
    hN V U hn G F F₀ D hreg hF₀ hF H u u' W T hTH hT hTfree h₁ h₂ hW hθ
  obtain ⟨R,hplus,hminus,hpresplus,hpresminus,hR,hsupp,hno,hSp,hSm,hid⟩:=
    ordinary_root_separated_factor_pair_hub_trade (G\F₀) H S T hST u u' hune (m+1)
      M₁ M₂ hpack₁ hcover₁ hpack₂ hcover₂ hedge hroot hSH
  have hp:=wheel_decomposition_conflict_recovery (G\F₀) F R H
    (fun v z=>(v∈S∪T∧z=u)∨(v∈S∧z=u')) (S∪T) (m+1) hR hSp hsupp hfree hplus
  have hm':=wheel_decomposition_conflict_recovery (G\F₀) F R H
    (fun v z=>(v∈S∪T∧z=u')∨(v∈S∧z=u)) (S∪T) (m+1) hR hSm hsupp hfree hminus
  exact ⟨S,hSH,hSc,hSW,hST,hfree,R,hplus,hminus,hp,hm',hR,hsupp,hno,hSp,hSm,hid⟩
end Oberwolfach
