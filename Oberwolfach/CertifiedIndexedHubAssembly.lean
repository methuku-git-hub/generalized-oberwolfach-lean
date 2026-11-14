module

public import Oberwolfach.OrdinaryHubTradeCertificate
public import Oberwolfach.OrdinaryHubTradeAssembly
public import Oberwolfach.OrdinaryProfileTransformerCompletion

@[expose] public section
/-! Assemble certified, row-disjoint hub switches with previously chosen
wheel families using their exact signed resource identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem assemble_indexed_ordinary_hub_trades {V U I J:Type} [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I] [Fintype J] {r:ℕ}
    (Q F:SimpleGraph V) (H:V→U→Prop) (W:Finset V)
    (A Z:I→Finset V) (u u':I→U)
    (hAW:∀ i,Disjoint (A i) W)
    (hpair:∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j))
    (hcert:∀ i,OrdinaryHubTradeCertificate Q F H (u i) (u' i) (A i) (Z i) r)
    (Plus Minus:J→OrdinaryWheel Q F H r)
    (hPlus:∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j)))
    (hMinus:∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j)))
    (hPW:∀ i,∀ v∈(ordinaryWheelRim (Plus i)).support,v∈W)
    (hMW:∀ i,∀ v∈(ordinaryWheelRim (Minus i)).support,v∈W)
    (hspokes:∀ i,∀ v∈Z i,¬wheelFamilySpokes Plus v (u' i)∧¬wheelFamilySpokes Minus v (u i))
    (L L':Finset (Sym2 V⊕(V×U))) (hLL:Disjoint L L')
    (hid:∀ e,(if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
      ∑ i,((if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
        (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))):
    ∃ K:Finset (Sym2 V⊕(V×U)),
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L L' K ∧
      K⊆ordinaryHostResources Q H ∧
      (∀ v w,Sum.inl s(v,w)∈K→
        Sum.inl s(v,w)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨
        ∃ i,v∈A i∨w∈A i) ∧
      (∀ v a,Sum.inr (v,a)∈K→
        Sum.inr (v,a)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨
        ∃ i,v∈A i∨v∈Z i) ∧
      (∀ v w,Sum.inl s(v,w)∈K→
        v∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion A∪Finset.univ.biUnion Z ∧
        w∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion A∪Finset.univ.biUnion Z) ∧
      (∀ v a,Sum.inr (v,a)∈K→
        v∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion A∪Finset.univ.biUnion Z):=by
  choose R hR using hcert
  let P:=ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)
  let P':=ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus)
  let Uplus:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v a=>(v∈A i∪Z i∧a=u i)∨(v∈A i∧a=u' i))
  let Uminus:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v a=>(v∈A i∪Z i∧a=u' i)∨(v∈A i∧a=u i))
  have hRsup (i:I) (v w:V) (hv:(R i).Adj v w):
      v∈A i∪Z i∧w∈A i∪Z i∧(v∈A i∨w∈A i):=by
    obtain ⟨_,_,_,_,_,hsupp,hno,_,_,_⟩:=hR i
    have hh:=hsupp v w hv
    refine ⟨hh.1,hh.2,?_⟩
    by_cases hvA:v∈A i
    · exact Or.inl hvA
    · by_cases hwA:w∈A i
      · exact Or.inr hwA
      · have hvZ:v∈Z i:=(Finset.mem_union.mp hh.1).resolve_left hvA
        have hwZ:w∈Z i:=(Finset.mem_union.mp hh.2).resolve_left hwA
        exact (hno v w hvZ hwZ hv).elim
  have hUplus:∀ i j,i≠j→Disjoint (Uplus i) (Uplus j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hpair i j hij) (fun v w hv=>(hRsup i v w hv).1) (fun v w hv=>(hRsup j v w hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hUminus:∀ i j,i≠j→Disjoint (Uminus i) (Uminus j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hpair i j hij) (fun v w hv=>(hRsup i v w hv).1) (fun v w hv=>(hRsup j v w hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hRow (C:J→OrdinaryWheel Q F H r) (hCW:∀ i,∀ v∈(ordinaryWheelRim (C i)).support,v∈W):
      (∀ v w,(wheelFamilyRim C).Adj v w→v∈W∧w∈W)∧
      (∀ v a,wheelFamilySpokes C v a→v∈W):=by
    constructor
    · intro v w hv
      obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hv
      exact ⟨hCW j v hj.mem_support_left,hCW j w hj.mem_support_right⟩
    · rintro v a ⟨j,_,hj⟩;exact hCW j v hj
  have hPU:∀ i,Disjoint P (Uminus i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u i) (u' i) (hAW i)
      (hRow Plus hPW).1 (hRow Plus hPW).2 (fun v w hv=>(hRsup i v w hv).2.2)
      (fun v hv=>(hspokes i v hv).1)
  have hP'U:∀ i,Disjoint P' (Uplus i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u' i) (u i) (hAW i)
      (hRow Minus hMW).1 (hRow Minus hMW).2 (fun v w hv=>(hRsup i v w hv).2.2)
      (fun v hv=>(hspokes i v hv).2)
  have hplus:∀ i,HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (Uplus i):=by
    intro i
    obtain ⟨_,_,hh,_,_,_,_,_,_,_⟩:=hR i
    exact hh
  have hminus:∀ i,HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (Uminus i):=by
    intro i
    obtain ⟨_,_,_,hh,_,_,_,_,_,_⟩:=hR i
    exact hh
  have hid' (i:I) (e:Sym2 V⊕(V×U)):
      (if e∈Uplus i then (1:ℤ) else 0)-(if e∈Uminus i then 1 else 0)=
      (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
      (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0):=by
    obtain ⟨_,_,_,_,_,_,_,_,_,hh⟩:=hR i
    exact hh e
  have hfinal:=resource_transformer_adjoin_trades
    (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L L' P P' Uplus Uminus
    hLL (wheelFamily_host_decomposition Plus hPlus) (wheelFamily_host_decomposition Minus hMinus)
    hplus hminus hUplus hUminus hPU hP'U (by
      intro e
      rw [hid e]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hid' i e).symm)
  dsimp only at hfinal
  let K:=(P∪Finset.univ.biUnion Uminus)\L
  refine ⟨K,hfinal.2,?_,?_,?_,?_,?_⟩
  · exact Finset.subset_union_left.trans (ordinary_host_decomposition_subhost _ hfinal.2.2.2.1)
  · intro v w hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hp|hp
    · exact Or.inl hp
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
      have hh:=hRsup i v w ((ordinaryHostResources_rim _ _ _).mp hi)
      exact Or.inr ⟨i,hh.2.2⟩
  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hp|hp
    · exact Or.inl hp
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      rcases hh with ⟨hv,_⟩|⟨hv,_⟩
      · exact Or.inr ⟨i,Finset.mem_union.mp hv⟩
      · exact Or.inr ⟨i,Or.inl hv⟩
  · intro v w hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hp|hp
    · have hh:(wheelFamilyRim Plus).Adj v w:=(ordinaryHostResources_rim _ _ _).mp hp
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh.mem_support_left)),
        Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh.mem_support_right))⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
      have hh:=hRsup i v w ((ordinaryHostResources_rim _ _ _).mp hi)
      have hin (x:V) (hx:x∈A i∪Z i):x∈(wheelFamilyRim Plus).support.toFinset∪Finset.univ.biUnion A∪Finset.univ.biUnion Z:=by
        rcases Finset.mem_union.mp hx with hx|hx
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩))
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)
      exact ⟨hin v hh.1,hin w hh.2.1⟩
  · intro v a hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hp|hp
    · obtain ⟨j,_,hj⟩:=(ordinaryHostResources_spoke _ _ _ _).mp hp
      have hh:v∈(wheelFamilyRim Plus).support:=by
        obtain ⟨w,hw⟩:=hj
        exact ⟨w,SimpleGraph.iSup_adj.mpr ⟨j,hw⟩⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh))
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hp
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v a).mp hi
      have hv':v∈A i∪Z i:=hh.elim And.left (fun h=>Finset.mem_union_left _ h.1)
      rcases Finset.mem_union.mp hv' with hvA|hvZ
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hvA⟩))
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hvZ⟩)

end Oberwolfach
