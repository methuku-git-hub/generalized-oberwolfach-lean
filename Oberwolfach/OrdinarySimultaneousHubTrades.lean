module

public import Oberwolfach.OrdinaryBoundedHostHubTrade
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Simultaneous actual hub trades from the common-weight/profile
hypotheses. Their size parameter precedes the conflict and forbidden-set
bounds. The old Z_i sets stay in the factor domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_simultaneous_hub_trades (r:ℕ) (hr:3≤r)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η∧∀ q p:ℕ,∃ t:ℕ,1≤t∧∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀∧
      ∀ (V U I:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I],
      Fintype.card I≤p→∀ (Q F:SimpleGraph V) (H:V→U→Prop) (T Z:I→Finset V) (u u':I→U)
      (k:I→ℝ) (z:I→ℕ) (W:Finset V),
      (∀ i,k₀≤k i)→(∀ i,u i≠u' i)→(∀ i,∀ v∈T i,H v (u i)∧H v (u' i))→
      (∀ i,((T i).card:ℝ)=r*k i)→(∀ v,(F.degree v:ℝ)≤D)→
      ∀ w:∀ i,LocalOrdinaryCycle Q F (T i) r→ℝ,
      (∀ i C,b/(k i)^(r-1)≤w i C∧w i C≤B/(k i)^(r-1))→
      (∀ i,∀ v∈T i,|1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i,∀ X:Finset V,X⊆T i→X.card=r→α*(k i)^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T i) (r:=r)) S X))→
      (W.card:ℝ)≤F₀→(∀ i,Z i⊆T i)→(∀ i,Z i⊆W)→(∀ i,(Z i).card=r*z i)→(∀ i,z i≤q)→
      (∀ i j,i≠j→Disjoint (Z i) (Z j))→
      ∃ (A:I→Finset V) (R:I→SimpleGraph V),
        (∀ i,A i⊆T i∧Disjoint (A i) W∧(A i).card=r*t∧
          (∀ x∈A i,∀ y∈A i,¬F.Adj x y)∧R i≤Q∧
          (∀ v w,(R i).Adj v w→v∈A i∪Z i∧w∈A i∪Z i∧(v∈A i∨w∈A i))∧
          (∀ v,(R i).degree v≤4)∧
          HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
            (ordinaryHostResources (R i) (fun v z=>(v∈A i∪Z i∧z=u i)∨(v∈A i∧z=u' i)))∧
          HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
            (ordinaryHostResources (R i) (fun v z=>(v∈A i∪Z i∧z=u' i)∨(v∈A i∧z=u i)))∧
          (∀ e:Sym2 V⊕(V×U),
            (if e∈ordinaryHostResources (R i) (fun v z=>(v∈A i∪Z i∧z=u i)∨(v∈A i∧z=u' i)) then (1:ℤ) else 0)-
            (if e∈ordinaryHostResources (R i) (fun v z=>(v∈A i∪Z i∧z=u' i)∨(v∈A i∧z=u i)) then 1 else 0)=
            (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
            (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)))∧
        (∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j))∧
        (∀ i j,i≠j→∀ v∈A i,∀ w∈A j,¬F.Adj v w):=by
  obtain ⟨η,hη,hbase⟩:=ordinary_bounded_host_hub_trade r hr S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q p
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  let F₁:ℝ:=F₀+p*(r*t)*(D+1)
  have hF₁:0≤F₁:=by dsimp only [F₁];positivity
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₁ D hF₁ hD
  refine ⟨k₀,hk₀,?_⟩
  intro V U I _ _ _ _ _ _ hI Q F H T Z u u' k z W hk hu hH hT hF w hw herr habs hW hZT hZW hZ hz hZZ
  let C:=Finset V×SimpleGraph V
  let Good:I→C→Prop:=fun i c=>
    c.1⊆T i∧Disjoint c.1 W∧c.1.card=r*t∧
    (∀ x∈c.1,∀ y∈c.1,¬F.Adj x y)∧c.2≤Q∧
    (∀ v w,c.2.Adj v w→v∈c.1∪Z i∧w∈c.1∪Z i∧(v∈c.1∨w∈c.1))∧
    (∀ v,c.2.degree v≤4)∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
            (ordinaryHostResources c.2 (fun v z=>(v∈c.1∪Z i∧z=u i)∨(v∈c.1∧z=u' i)))∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
            (ordinaryHostResources c.2 (fun v z=>(v∈c.1∪Z i∧z=u' i)∨(v∈c.1∧z=u i)))∧
    (∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources c.2 (fun v z=>(v∈c.1∪Z i∧z=u i)∨(v∈c.1∧z=u' i)) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources c.2 (fun v z=>(v∈c.1∪Z i∧z=u' i)∨(v∈c.1∧z=u i)) then 1 else 0)=
      (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
      (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))
  have hchoose:∀ i,∀ K:Finset V,(K.card:ℝ)≤(∅:Finset V).card+Fintype.card I*(r*t)*(D+1)→
      ∃ c:C,Good i c∧c.1.card≤r*t∧Disjoint c.1 K:=by
    intro i K hK
    have hIr:(Fintype.card I:ℝ)≤p:=by exact_mod_cast hI
    have hKr:(K.card:ℝ)≤p*(r*t)*(D+1):=by
      have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIr (by positivity:0≤(r:ℝ)*t))
        (by linarith:0≤D+1)
      simp only [Finset.card_empty,Nat.cast_zero,zero_add,Nat.cast_mul] at hK
      exact hK.trans hh
    have hWK:((W∪K).card:ℝ)≤F₁:=by
      have hh:((W∪K).card:ℝ)≤W.card+K.card:=by exact_mod_cast Finset.card_union_le W K
      dsimp only [F₁];linarith only [hh,hW,hKr]
    obtain ⟨A,R,hAT,hAI,hAc,hAF,hRQ,hRsup,hRdeg,hplus,hminus,hid⟩:=
      hbase (k i) (hk i) V U Q F H (T i) (u i) (u' i) (hu i) (hH i) (hT i) hF
        (w i) (hw i) (herr i) (habs i) (W∪K) (Z i) (z i) hWK (hZT i) (hZ i) (hz i)
    have hAW:Disjoint A W:=hAI.mono_right (fun v hv=>Finset.mem_union_right _ (Finset.mem_union_left _ hv))
    have hAK:Disjoint A K:=hAI.mono_right (fun v hv=>Finset.mem_union_right _ (Finset.mem_union_right _ hv))
    exact ⟨(A,R),⟨hAT,hAW,hAc,hAF,hRQ,hRsup,hRdeg,hplus,hminus,hid⟩,hAc.le,hAK⟩
  obtain ⟨f,hf,hsep⟩:=finite_conflict_separated_choices (fun c:C=>c.1) Good ∅ (r*t) F D hD hF (by simpa only [Nat.cast_mul] using hchoose)
  refine ⟨(fun i=>(f i).1),(fun i=>(f i).2),(fun i=>(hf i).1),?_,?_⟩
  · intro i j hij
    have hi:=(hf i).1.2.1
    have hj:=(hf j).1.2.1
    exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr
      ⟨(hsep i j hij).1,hi.mono_right (hZW j)⟩,
      Finset.disjoint_union_right.mpr ⟨(hj.mono_right (hZW i)).symm,hZZ i j hij⟩⟩
  · intro i j hij
    exact (hsep i j hij).2

end Oberwolfach
