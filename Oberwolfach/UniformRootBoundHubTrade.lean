module

public import Oberwolfach.UniformSpokeHubTrade

@[expose] public section
/-! The selected separated factors yield the two actual wheel
decompositions and the exact spoke trade at a pair of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_spoke_hub_trade_uniform_root_bound (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ q:ℕ,∃ t:ℕ,∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card V→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (H:V→U→Prop) (u u':U),u≠u'→∀ (W T:Finset V) (z:ℕ),z≤q→
    (∀ v∈T,H v u∧H v u')→T.card=(m+1)*z→(∀ x∈T,∀ y∈T,¬F.Adj x y)→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ξ*Fintype.card V→
    (((Finset.univ:Finset V).filter (fun v=>¬H v u')).card:ℝ)≤ξ*Fintype.card V→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∃ S:Finset V,(∀ v∈S∪T,H v u∧H v u') ∧ S.card≤t ∧ Disjoint S W ∧ Disjoint S T ∧
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
        (if e∈T.image (fun v=>Sum.inr (v,u')) then 1 else 0)) :=by
  obtain ⟨ξ,hξ,hbase⟩:=regular_host_spoke_hub_trade_uniform m hm α hα hα1
  refine ⟨ξ,hξ,?_⟩
  intro q
  have hex (z:Fin (q+1)):=hbase ((m+1)*z.val) (dvd_mul_right _ _)
  choose k hk hbasez using hex
  let t:ℕ:=Finset.univ.sup k
  refine ⟨t,?_⟩
  intro L f hL
  choose Ns hNs using fun z:Fin (q+1)=>hbasez z L f hL
  let N:ℕ:=Finset.univ.sup Ns
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn G F F₀ D hreg hF₀ hF H u u' hune W T z hz hTH hT hTfree h₁ h₂ hW hθ
  let z':Fin (q+1):=⟨z,by omega⟩
  have hnz:Ns z'≤Fintype.card V:=(Finset.le_sup (s:=Finset.univ) (f:=Ns) (Finset.mem_univ z')).trans hn
  obtain ⟨S,hSH,hSc,hSW,hST,hfree,R,hplus,hminus,hp,hm',hR,hsupp,hno,hSp,hSm,hid⟩:=
    hNs z' V U hnz G F F₀ D hreg hF₀ hF H u u' hune W T hTH (by simpa [z'] using hT) hTfree h₁ h₂ hW hθ
  have hkt:k z'≤t:=Finset.le_sup (s:=Finset.univ) (f:=k) (Finset.mem_univ z')
  exact ⟨S,hSH,hSc.le.trans hkt,hSW,hST,hfree,R,hplus,hminus,hp,hm',hR,hsupp,hno,hSp,hSm,hid⟩
end Oberwolfach
