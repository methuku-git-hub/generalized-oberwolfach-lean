module

public import Oberwolfach.TriangleTransformerSimultaneousTrades
public import Oberwolfach.OrdinaryHubTradeAssembly
public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section
/-! Assemble the checked triangle hub trades with an already constructed
pair of vertex-wheel families, using their exact resource identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem triangle_selected_hub_trades_finish
    (G:SimpleGraph V) (H:V→U→Prop) (A Z:I→Finset V) (u u':I→U)
    (R:I→SimpleGraph V) (W:Finset V) (s K₀:ℕ)
    (hI:Fintype.card I≤K₀)
    (hA:∀ i,(A i).card=s ∧ Disjoint (A i) W)
    (hZW:∀ i,Z i⊆W)
    (hpair:∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j))
    (hR:∀ i,TriangleHubTradeAt G H (A i) (Z i) (u i) (u' i) (R i))
    (Plus Minus:J→OrdinaryWheel G ⊥ H 3)
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
    ∃ N:Finset V,∃ T:Finset (Sym2 V⊕(V×U)),
      Disjoint N W ∧ N.card≤K₀*s ∧
      IsResourceTransformer (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) L L' T ∧
      (∀ v w,Sum.inl s(v,w)∈T→v∈W∪N∧w∈W∪N) ∧
      (∀ v z,Sum.inr (v,z)∈T→v∈W∪N) ∧
      (∀ v w,Sum.inl s(v,w)∈T→
        Sum.inl s(v,w)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨v∈N∨w∈N) ∧
      (∀ v z,Sum.inr (v,z)∈T→
        Sum.inr (v,z)∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)∨v∈N∨∃ i,v∈Z i) ∧
      (∀ v w,Sum.inl s(v,w)∈T→
        (v∈(wheelFamilyRim Plus).support.toFinset∨v∈N∨∃ i,v∈Z i) ∧
        (w∈(wheelFamilyRim Plus).support.toFinset∨w∈N∨∃ i,w∈Z i)) ∧
      (∀ v z,Sum.inr (v,z)∈T→wheelFamilySpokes Plus v z∨∃ i,z=u i∨z=u' i) :=by
  let P:=ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus)
  let P':=ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus)
  let Up:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v z=>(v∈A i∪Z i∧z=u i)∨(v∈A i∧z=u' i))
  let Um:I→Finset (Sym2 V⊕(V×U)):=fun i=>ordinaryHostResources (R i)
    (fun v z=>(v∈A i∪Z i∧z=u' i)∨(v∈A i∧z=u i))
  have hsupport (i:I) (v w:V) (hv:(R i).Adj v w):
      v∈A i∪Z i∧w∈A i∪Z i∧(v∈A i∨w∈A i):=by
    obtain ⟨_,_,_,_,_,hsupp,hno,_,_,_⟩:=hR i
    have h:=hsupp v w hv
    refine ⟨h.1,h.2,?_⟩
    by_contra hn
    have hna: v∉A i∧w∉A i:=by tauto
    have hvz:v∈Z i:=(Finset.mem_union.mp h.1).resolve_left hna.1
    have hwz:w∈Z i:=(Finset.mem_union.mp h.2).resolve_left hna.2
    exact hno v w hvz hwz hv
  have hUplus:∀ i j,i≠j→Disjoint (Up i) (Up j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hpair i j hij) (fun v w hv=>(hsupport i v w hv).1) (fun v w hv=>(hsupport j v w hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hUminus:∀ i j,i≠j→Disjoint (Um i) (Um j):=by
    intro i j hij
    exact ordinary_resources_disjoint_of_row_support (R i) (R j) _ _ (A i∪Z i) (A j∪Z j)
      (hpair i j hij) (fun v w hv=>(hsupport i v w hv).1) (fun v w hv=>(hsupport j v w hv).1)
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
      (fun v _ hv=>hv.elim And.left (fun hh=>Finset.mem_union_left _ hh.1))
  have hRow (C:J→OrdinaryWheel G ⊥ H 3) (hCW:∀ i,∀ v∈(ordinaryWheelRim (C i)).support,v∈W):
      (∀ v w,(wheelFamilyRim C).Adj v w→v∈W∧w∈W)∧(∀ v z,wheelFamilySpokes C v z→v∈W):=by
    constructor
    · intro v w hv
      obtain ⟨j,hj⟩:=SimpleGraph.iSup_adj.mp hv
      exact ⟨hCW j v hj.mem_support_left,hCW j w hj.mem_support_right⟩
    · rintro v z ⟨j,_,hj⟩;exact hCW j v hj
  have hPU:∀ i,Disjoint P (Um i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u i) (u' i) (hA i).2
      (hRow Plus hPW).1 (hRow Plus hPW).2 (fun v w hv=>(hsupport i v w hv).2.2)
      (fun v hv=>(hspokes i v hv).1)
  have hP'U:∀ i,Disjoint P' (Up i):=by
    intro i
    exact ordinary_hub_trade_avoids_previous _ (R i) _ (A i) (Z i) W (u' i) (u i) (hA i).2
      (hRow Minus hMW).1 (hRow Minus hMW).2 (fun v w hv=>(hsupport i v w hv).2.2)
      (fun v hv=>(hspokes i v hv).2)
  have hUp (i:I):HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) (Up i):=by
    obtain ⟨_,_,hp,_,_,_,_,_,_,_⟩:=hR i
    exact hp
  have hUm (i:I):HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) (Um i):=by
    obtain ⟨_,_,_,hm,_,_,_,_,_,_⟩:=hR i
    exact hm
  have hident (i:I) (e:Sym2 V⊕(V×U)):
      (if e∈Up i then (1:ℤ) else 0)-(if e∈Um i then 1 else 0)=
      (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
      (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0):=by
    obtain ⟨_,_,_,_,_,_,_,_,_,hh⟩:=hR i
    exact hh e
  have hfinal:=resource_transformer_adjoin_trades
    (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) L L' P P' Up Um
    hLL (wheelFamily_host_decomposition Plus hPlus) (wheelFamily_host_decomposition Minus hMinus)
    hUp hUm hUplus hUminus hPU hP'U (by
      intro e
      rw [hid e]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (hident i e).symm)
  dsimp only at hfinal
  let N:=Finset.univ.biUnion A
  let T:=(P∪Finset.univ.biUnion Um)\L
  have hAN (i:I):A i⊆N:=fun v hv=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩
  have hAZ (i:I):A i∪Z i⊆W∪N:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_right _ (hAN i hv)
    · exact Finset.mem_union_left _ (hZW i hv)
  refine ⟨N,T,?_,?_,hfinal.2,?_,?_,?_,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hvW
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact Finset.disjoint_left.mp (hA i).2 hi hvW
  · calc
      N.card≤∑ i,(A i).card:=Finset.card_biUnion_le
      _=Fintype.card I*s:=by simp only [(fun i=>(hA i).1),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
      _≤K₀*s:=Nat.mul_le_mul_right _ hI
  · intro v w hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · have hh:=(hRow Plus hPW).1 v w ((ordinaryHostResources_rim _ _ _).mp hv)
      exact ⟨Finset.mem_union_left _ hh.1,Finset.mem_union_left _ hh.2⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hsupport i v w ((ordinaryHostResources_rim _ _ _).mp hi)
      exact ⟨hAZ i hh.1,hAZ i hh.2.1⟩
  · intro v z hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Finset.mem_union_left _ ((hRow Plus hPW).2 v z ((ordinaryHostResources_spoke _ _ _ _).mp hv))
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v z).mp hi
      exact hAZ i (hh.elim And.left (fun h=>Finset.mem_union_left _ h.1))
  · intro v w hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl hv
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hsupport i v w ((ordinaryHostResources_rim _ _ _).mp hi)
      exact Or.inr (hh.2.2.imp (fun h=>hAN i h) (fun h=>hAN i h))
  · intro v z hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl hv
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v z).mp hi
      rcases hh with ⟨hv,_⟩|⟨hv,_⟩
      · rcases Finset.mem_union.mp hv with hv|hv
        · exact Or.inr (Or.inl (hAN i hv))
        · exact Or.inr (Or.inr ⟨i,hv⟩)
      · exact Or.inr (Or.inl (hAN i hv))
  · intro v w hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · have hh:(wheelFamilyRim Plus).Adj v w:=(ordinaryHostResources_rim _ _ _).mp hv
      exact ⟨Or.inl (Set.mem_toFinset.mpr hh.mem_support_left),Or.inl (Set.mem_toFinset.mpr hh.mem_support_right)⟩
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=hsupport i v w ((ordinaryHostResources_rim _ _ _).mp hi)
      constructor
      · rcases Finset.mem_union.mp hh.1 with ha|hz
        · exact Or.inr (Or.inl (hAN i ha))
        · exact Or.inr (Or.inr ⟨i,hz⟩)
      · rcases Finset.mem_union.mp hh.2.1 with ha|hz
        · exact Or.inr (Or.inl (hAN i ha))
        · exact Or.inr (Or.inr ⟨i,hz⟩)
  · intro v z hv
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hv).1 with hv|hv
    · exact Or.inl ((ordinaryHostResources_spoke _ _ _ _).mp hv)
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      have hh:=(ordinaryHostResources_spoke (R i)
        (fun x y=>(x∈A i∪Z i∧y=u' i)∨(x∈A i∧y=u i)) v z).mp hi
      rcases hh with ⟨_,hz⟩|⟨_,hz⟩
      · exact Or.inr ⟨i,Or.inr hz⟩
      · exact Or.inr ⟨i,Or.inl hz⟩
end Oberwolfach
