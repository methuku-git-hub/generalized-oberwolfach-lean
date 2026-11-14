module

public import Oberwolfach.UniformIndexedHubTrades
public import Oberwolfach.CertifiedIndexedHubAssembly

@[expose] public section
/-! Actual separated hub trades in a regular host close the transformer
whenever the previously constructed wheel families satisfy the displayed
physical resource identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_host_indexed_hub_transformer_uniform_named_subgraph (m:ℕ) (hm:2≤m) (α:ℝ)
    (hα:0<α) (hα1:α≤1):
    ∃ ξ:ℝ,0<ξ ∧ ∀ q p:ℕ,∃ t:ℕ,∀ (L:ℝ) (f:ℕ),0≤L→∃ N:ℕ,
    ∀ (V U I J:Type) [Fintype V] [Fintype U] [Fintype I] [Fintype J] [DecidableEq V] [DecidableEq U] [DecidableEq I],N≤Fintype.card V→Fintype.card I≤p→
    ∀ (G F F₀:SimpleGraph V) (D:ℕ),G.IsRegularOfDegree D→F₀.edgeFinset.card≤f→
    (∀ v,(F.degree v:ℝ)≤L)→∀ (Q:SimpleGraph V),Q=G\F₀→∀ (H:V→U→Prop) (u u':I→U) (W:Finset V)
      (T:I→Finset V) (z:I→ℕ),
    (∀ i,u i≠u' i)→(∀ i,z i≤q)→(∀ i,(T i).card=(m+1)*z i)→
    (∀ i,T i⊆W)→(∀ i j,i≠j→Disjoint (T i) (T j))→
    (∀ i,∀ v∈T i,H v (u i)∧H v (u' i))→
    (∀ i,∀ x∈T i,∀ y∈T i,¬F.Adj x y)→
    (∀ i,(((Finset.univ:Finset V).filter (fun v=>¬H v (u i))).card:ℝ)≤ξ*Fintype.card V)→
    (∀ i,(((Finset.univ:Finset V).filter (fun v=>¬H v (u' i))).card:ℝ)≤ξ*Fintype.card V)→
    (W.card:ℝ)≤ξ*Fintype.card V→
    cycleThreshold (m+1)+α≤(D:ℝ)/Fintype.card V→
    ∀ Plus Minus:J→OrdinaryWheel (Q) F H (m+1),
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)))→
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)))→
    (∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈W)→
    (∀ i,∀ v∈(ordinaryWheelRim (Minus i)).support,v∈W)→
    (∀ i,∀ v∈T i,¬wheelFamilySpokes Plus v (u' i)∧¬wheelFamilySpokes Minus v (u i))→
    ∀ X X':Finset (Sym2 V⊕(V×U)),Disjoint X X'→
    (∀ e,(if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈X then 1 else 0)-(if e∈X' then 1 else 0)+
      ∑ i,((if e∈(T i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
        (if e∈(T i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)))→
    ∃ S:I→Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
      (∀ i,(S i).card≤t ∧ Disjoint (S i) W) ∧
      (∀ i j,i≠j→Disjoint (S i∪T i) (S j∪T j)) ∧
      (∀ i j,i≠j→∀ x∈S i,∀ y∈S j,¬F.Adj x y) ∧
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=m+1)) X X' K ∧
      K⊆ordinaryHostResources (Q) H ∧
      (∀ v w,Sum.inl s(v,w)∈K→
        Sum.inl s(v,w)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨
        ∃ i,v∈S i∨w∈S i) ∧
      (∀ v a,Sum.inr (v,a)∈K→
        Sum.inr (v,a)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨
        ∃ i,v∈S i∨v∈T i) ∧
      (∀ v w,Sum.inl s(v,w)∈K→
        v∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion S∪Finset.univ.biUnion T ∧
        w∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion S∪Finset.univ.biUnion T) ∧
      (∀ v a,Sum.inr (v,a)∈K→
        v∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion S∪Finset.univ.biUnion T):=by
  obtain ⟨ξ,hξ,hbase⟩:=regular_host_indexed_hub_trades_uniform m hm α hα hα1
  refine ⟨ξ,hξ,?_⟩
  intro q p
  obtain ⟨t,hbase⟩:=hbase q p
  refine ⟨t,?_⟩
  intro L f hL
  obtain ⟨N,hN⟩:=hbase L f hL
  refine ⟨N,?_⟩
  intro V U I J _ _ _ _ _ _ _ hn hI G F F₀ D hreg hF₀ hF Q hQeq H u u' W T z hune hz hT hTW hTT hTH hTfree h₁ h₂ hW hθ
    Plus Minus hPlus hMinus hPW hMW hspokes X X' hXX hid
  subst Q
  obtain ⟨S,hS,hpair,hsep⟩:=hN V U I hn hI G F F₀ D hreg hF₀ hF H u u' W T z
    hune hz hT hTW hTT hTH hTfree h₁ h₂ hW hθ
  obtain ⟨K,hK,hKsub,hnewR,hnewS,hExactR,hExactS⟩:=assemble_indexed_ordinary_hub_trades (G\F₀) F H W S T u u'
    (fun i=>(hS i).2.1) hpair (fun i=>(hS i).2.2.2.2.2)
    Plus Minus hPlus hMinus hPW hMW hspokes X X' hXX hid
  exact ⟨S,K,(fun i=>⟨(hS i).1,(hS i).2.1⟩),hpair,hsep,hK,hKsub,hnewR,hnewS,hExactR,hExactS⟩
end Oberwolfach
