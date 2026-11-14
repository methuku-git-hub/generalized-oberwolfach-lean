module

public import Oberwolfach.OrdinarySimultaneousHubTrades
public import Oberwolfach.OrdinaryHubTradeAssembly
public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section

/-! Finish an actual wheel construction with hub trades obtained from
its supplied cycle weights and absorber counts. No hub-trade or factor
existence is an input. The size of the new row set precedes the later
forbidden-set bound; wheel witnesses retain the original host and F. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem ordinary_host_decomposition_subhost {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (L:Finset (Sym2 V⊕(V×U)))
    (h:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L):
    L⊆ordinaryHostResources Q H:=by
  obtain ⟨M,_,hM⟩:=h
  intro e he
  rw [←hM] at he
  obtain ⟨W,_,hW⟩:=Finset.mem_biUnion.mp he
  exact ((ordinaryWheelResources_subset_host W Q H).mpr ⟨W.val.1.property,W.property.1⟩) hW

 theorem ordinary_profile_transformer_completion (r:ℕ) (hr:3≤r)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η∧∀ q p:ℕ,∃ t:ℕ,1≤t∧∀ F₀ d:ℝ,0≤F₀→0≤d→
      ∃ k₀:ℝ,1<k₀∧
      ∀ (V U I J:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype I] [DecidableEq I] [Fintype J],Fintype.card I≤p→
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (T Z:I→Finset V) (u u':I→U)
      (k:I→ℝ) (z:I→ℕ) (W:Finset V),
      (∀ i,k₀≤k i)→(∀ i,u i≠u' i)→(∀ i,∀ v∈T i,H v (u i)∧H v (u' i))→
      (∀ i,((T i).card:ℝ)=r*k i)→(∀ v,(F.degree v:ℝ)≤d)→
      ∀ w:∀ i,LocalOrdinaryCycle Q F (T i) r→ℝ,
      (∀ i C,b/(k i)^(r-1)≤w i C∧w i C≤B/(k i)^(r-1))→
      (∀ i,∀ v∈T i,|1-hypergraphWeightedDegree localOrdinaryVertices (w i) v|≤η)→
      (∀ i,∀ X:Finset V,X⊆T i→X.card=r→α*(k i)^(r*r)≤
        Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T i) (r:=r)) S X))→
      (W.card:ℝ)≤F₀→(∀ i,Z i⊆T i)→(∀ i,Z i⊆W)→(∀ i,(Z i).card=r*z i)→(∀ i,z i≤q)→
      (∀ i j,i≠j→Disjoint (Z i) (Z j))→
      ∀ Plus Minus:J→OrdinaryWheel Q F H r,
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)))→
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)))→
      (∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈W)→
      (∀ i,∀ v∈(ordinaryWheelRim (Minus i)).support,v∈W)→
      (∀ i,∀ v∈Z i,¬wheelFamilySpokes Plus v (u' i)∧¬wheelFamilySpokes Minus v (u i))→
      ∀ L L':Finset (Sym2 V⊕(V×U)),Disjoint L L'→
      (∀ e,(if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
        (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
        (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
        ∑ i,((if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)))→
      ∃ N:Finset V,∃ K:Finset (Sym2 V⊕(V×U)),
        Disjoint N W∧N.card≤p*(r*t)∧
        IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L L' K∧
        K⊆ordinaryHostResources Q H∧
        (∀ v v',Sum.inl s(v,v')∈K→v∈W∪N∧v'∈W∪N)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈W∪N)∧
        (∀ v v',Sum.inl s(v,v')∈K→
          Sum.inl s(v,v')∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨v∈N∨v'∈N)∧
        (∀ v a,Sum.inr (v,a)∈K→
          Sum.inr (v,a)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨v∈N∨∃ i,v∈Z i)∧
        (∀ v v',Sum.inl s(v,v')∈K→
          v∈(wheelFamilyRim Plus).support.toFinset∪N∪Finset.univ.biUnion Z∧
          v'∈(wheelFamilyRim Plus).support.toFinset∪N∪Finset.univ.biUnion Z)∧
        (∀ v a,Sum.inr (v,a)∈K→v∈(wheelFamilyRim Plus).support.toFinset∪N∪Finset.univ.biUnion Z)∧
        (∀ v a,Sum.inr (v,a)∈K→wheelFamilySpokes Plus v a∨∃ i,a=u i∨a=u' i)∧
        N⊆Finset.univ.biUnion T:=by
  obtain ⟨η,hη,hbase⟩:=ordinary_simultaneous_hub_trades r hr S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q p
  obtain ⟨t,ht,hbase⟩:=hbase q p
  refine ⟨t,ht,?_⟩
  intro F₀ d hF₀ hd
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ d hF₀ hd
  refine ⟨k₀,hk₀,?_⟩
  intro V U I J _ _ _ _ _ _ _ hI Q F H T Z u u' k z W hk hu hH hT hF w hw herr habs hW hZT hZW hZ hz hZZ
    Plus Minus hPlus hMinus hPW hMW hspokes L L' hLL hid
  obtain ⟨A,R,hA,hdis,_⟩:=hbase V U I hI Q F H T Z u u' k z W hk hu hH hT hF
    w hw herr habs hW hZT hZW hZ hz hZZ
  let P:=ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)
  let P':=ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus)
  let Uplus:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v a=>(v∈A i∪Z i∧a=u i)∨(v∈A i∧a=u' i))
  let Uminus:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v a=>(v∈A i∪Z i∧a=u' i)∨(v∈A i∧a=u i))
  have hRsup (i:I) (v v':V) (hv:(R i).Adj v v'):
      v∈A i∪Z i∧v'∈A i∪Z i∧(v∈A i∨v'∈A i):=(hA i).2.2.2.2.2.1 v v' hv
  have hUplus:∀ i j,i≠j→Disjoint (Uplus i) (Uplus j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hdis i j hij) (fun v v' hv=>(hRsup i v v' hv).1) (fun v v' hv=>(hRsup j v v' hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hUminus:∀ i j,i≠j→Disjoint (Uminus i) (Uminus j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hdis i j hij) (fun v v' hv=>(hRsup i v v' hv).1) (fun v v' hv=>(hRsup j v v' hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hRow (C:J→OrdinaryWheel Q F H r) (hCW:∀ i,∀ v∈(ordinaryWheelRim (C i)).support,v∈W):
      (∀ v v',(wheelFamilyRim C).Adj v v'→v∈W∧v'∈W)∧
      (∀ v a,wheelFamilySpokes C v a→v∈W):=by
    constructor
    · intro v v' hv
      obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hv
      exact ⟨hCW j v hj.mem_support_left,hCW j v' hj.mem_support_right⟩
    · rintro v a ⟨j,_,hj⟩;exact hCW j v hj
  have hPU:∀ i,Disjoint P (Uminus i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u i) (u' i) (hA i).2.1
      (hRow Plus hPW).1 (hRow Plus hPW).2 (fun v v' hv=>(hRsup i v v' hv).2.2)
      (fun v hv=>(hspokes i v hv).1)
  have hP'U:∀ i,Disjoint P' (Uplus i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u' i) (u i) (hA i).2.1
      (hRow Minus hMW).1 (hRow Minus hMW).2 (fun v v' hv=>(hRsup i v v' hv).2.2)
      (fun v hv=>(hspokes i v hv).2)
  have hfinal:=resource_transformer_adjoin_trades
    (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L L' P P' Uplus Uminus
    hLL (wheelFamily_host_decomposition Plus hPlus) (wheelFamily_host_decomposition Minus hMinus)
    (fun i=>(hA i).2.2.2.2.2.2.2.1) (fun i=>(hA i).2.2.2.2.2.2.2.2.1)
    hUplus hUminus hPU hP'U (by
      intro e
      rw [hid e]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact ((hA i).2.2.2.2.2.2.2.2.2 e).symm)
  dsimp only at hfinal
  let N:=Finset.univ.biUnion A
  let K:=(P∪Finset.univ.biUnion Uminus)\L
  have hK:IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L L' K:=hfinal.2
  have hAN (i:I):A i⊆N:=fun v hv=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩
  have hAZ (i:I):A i∪Z i⊆W∪N:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_right _ (hAN i hv)
    · exact Finset.mem_union_left _ (hZW i hv)
  have hExactAZ (i:I):A i∪Z i⊆(wheelFamilyRim Plus).support.toFinset∪N∪Finset.univ.biUnion Z:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hAN i hv))
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩)
  refine ⟨N,K,?_,?_,hK,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hvW
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hA i).2.1 hi hvW
  · calc
      N.card≤∑ i,(A i).card:=Finset.card_biUnion_le
      _=Fintype.card I*(r*t):=by simp only [(fun i=>(hA i).2.2.1),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤p*(r*t):=Nat.mul_le_mul_right _ hI
  · exact Finset.subset_union_left.trans (ordinary_host_decomposition_subhost _ hK.2.2.1)
  · intro v v' hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · have hh:=(hRow Plus hPW).1 v v' ((ordinaryHostResources_rim _ _ _).mp hv)
      exact ⟨Finset.mem_union_left _ hh.1,Finset.mem_union_left _ hh.2⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hRsup i v v' ((ordinaryHostResources_rim _ _ _).mp hi)
      exact ⟨hAZ i hh.1,hAZ i hh.2.1⟩
  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Finset.mem_union_left _ ((hRow Plus hPW).2 v a ((ordinaryHostResources_spoke _ _ _ _).mp hv))
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      exact hAZ i (hh.elim And.left (fun h=>Finset.mem_union_left _ h.1))

  · intro v v' hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl hv
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hRsup i v v' ((ordinaryHostResources_rim _ _ _).mp hi)
      exact Or.inr (hh.2.2.imp (fun h=>hAN i h) (fun h=>hAN i h))
  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl hv
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      rcases hh with ⟨hv,_⟩|⟨hv,_⟩
      · rcases Finset.mem_union.mp hv with hv|hv
        · exact Or.inr (Or.inl (hAN i hv))
        · exact Or.inr (Or.inr ⟨i,hv⟩)
      · exact Or.inr (Or.inl (hAN i hv))

  · intro v v' hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · have hh:(wheelFamilyRim Plus).Adj v v':=(ordinaryHostResources_rim _ _ _).mp hv
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh.mem_support_left)),
        Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh.mem_support_right))⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hRsup i v v' ((ordinaryHostResources_rim _ _ _).mp hi)
      exact ⟨hExactAZ i hh.1,hExactAZ i hh.2.1⟩
  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · obtain ⟨j,_,hj⟩:=(ordinaryHostResources_spoke _ _ _ _).mp hv
      have hh:v∈(wheelFamilyRim Plus).support:=by
        obtain ⟨w,hw⟩:=hj
        exact ⟨w,SimpleGraph.iSup_adj.mpr ⟨j,hw⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh))
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      exact hExactAZ i (hh.elim And.left (fun h=>Finset.mem_union_left _ h.1))

  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl ((ordinaryHostResources_spoke _ _ _ _).mp hv)
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      exact Or.inr ⟨i,hh.elim (fun h=>Or.inr h.2) (fun h=>Or.inl h.2)⟩

  · intro v hv
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,(hA i).1 hi⟩

end Oberwolfach
