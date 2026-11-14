module

public import Oberwolfach.OrdinaryExactDecomposition
public import Oberwolfach.ResourceTransformers

@[expose] public section

/-! Physical assembly of hub trades. New trade edges meet fresh row
labels; the retained Z labels use only the opposite hub. The final
transformer is extracted from an exact integer identity, not from edge counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem ordinary_resources_disjoint_of_row_support (Q Q':SimpleGraph V) (H H':V→U→Prop)
    (A A':Finset V) (hAA:Disjoint A A')
    (hQ:∀ v w,Q.Adj v w→v∈A) (hQ':∀ v w,Q'.Adj v w→v∈A')
    (hH:∀ v u,H v u→v∈A) (hH':∀ v u,H' v u→v∈A'):
    Disjoint (ordinaryHostResources Q H) (ordinaryHostResources Q' H'):=by
  apply ordinaryHostResources_disjoint
  · apply disjoint_iff_inf_le.mpr
    intro v w hh
    exact (Finset.disjoint_left.mp hAA (hQ v w hh.1) (hQ' v w hh.2)).elim
  · intro v u hh
    exact Finset.disjoint_left.mp hAA (hH v u hh.1) (hH' v u hh.2)

 theorem ordinary_hub_trade_avoids_previous (P R:SimpleGraph V) (K:V→U→Prop)
    (A Z W:Finset V) (u u':U) (hAW:Disjoint A W)
    (hP:∀ v w,P.Adj v w→v∈W∧w∈W) (hK:∀ v z,K v z→v∈W)
    (hR:∀ v w,R.Adj v w→v∈A∨w∈A)
    (hZ:∀ v∈Z,¬K v u'):
    Disjoint (ordinaryHostResources P K)
      (ordinaryHostResources R (fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u))):=by
  apply ordinaryHostResources_disjoint
  · apply disjoint_iff_inf_le.mpr
    intro v w hh
    rcases hR v w hh.2 with hv|hw
    · exact (Finset.disjoint_left.mp hAW hv (hP v w hh.1).1).elim
    · exact (Finset.disjoint_left.mp hAW hw (hP v w hh.1).2).elim
  · intro v z hh
    rcases hh.2 with ⟨hv,hz⟩|⟨hv,hz⟩
    · rcases Finset.mem_union.mp hv with hv|hv
      · exact Finset.disjoint_left.mp hAW hv (hK v z hh.1)
      · exact hZ v hv (hz ▸ hh.1)
    · exact Finset.disjoint_left.mp hAW hv (hK v z hh.1)

 theorem resource_transformer_from_disjoint_root_identity {X C:Type} [DecidableEq X] [DecidableEq C]
    (resources:C→Finset X) (L L' A B:Finset X) (hLL:Disjoint L L')
    (hA:HasResourceDecomposition resources A) (hB:HasResourceDecomposition resources B)
    (hid:∀ e,(if e∈A then (1:ℤ) else 0)-(if e∈B then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)):
    A\L=B\L'∧IsResourceTransformer resources L L' (A\L):=by
  have hLeft (e:X) (he:e∈L):e∈A∧e∉B:=by
    have he':e∉L':=fun hh=>Finset.disjoint_left.mp hLL he hh
    have hi:=hid e
    simp only [he,he',ite_true,ite_false] at hi
    by_cases ha:e∈A <;> by_cases hb:e∈B <;> simp only [ha,hb,ite_true,ite_false] at hi <;> simp_all
  have hRight (e:X) (he:e∈L'):e∈B∧e∉A:=by
    have he':e∉L:=fun hh=>Finset.disjoint_left.mp hLL hh he
    have hi:=hid e
    simp only [he,he',ite_true,ite_false] at hi
    by_cases ha:e∈A <;> by_cases hb:e∈B <;> simp only [ha,hb,ite_true,ite_false] at hi <;> simp_all
  exact resource_transformer_of_indicator_identity resources L L' A B hA hB
    (fun e he=>(hLeft e he).1) (fun e he=>(hRight e he).1)
    (Finset.disjoint_left.mpr (fun e he=>(hLeft e he).2))
    (Finset.disjoint_left.mpr (fun e he=>(hRight e he).2)) hid

 theorem resource_transformer_adjoin_trades {X C I:Type} [DecidableEq X] [DecidableEq C]
    [Fintype I] [DecidableEq I]
    (resources:C→Finset X) (L L' P P':Finset X) (A A':I→Finset X)
    (hLL:Disjoint L L') (hP:HasResourceDecomposition resources P) (hP':HasResourceDecomposition resources P')
    (hA:∀ i,HasResourceDecomposition resources (A i)) (hA':∀ i,HasResourceDecomposition resources (A' i))
    (hAA:∀ i j,i≠j→Disjoint (A i) (A j)) (hAA':∀ i j,i≠j→Disjoint (A' i) (A' j))
    (hPA':∀ i,Disjoint P (A' i)) (hP'A:∀ i,Disjoint P' (A i))
    (hid:∀ e,(if e∈P then (1:ℤ) else 0)-(if e∈P' then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
      ∑ i,((if e∈A i then 1 else 0)-(if e∈A' i then 1 else 0))):
    let D:=P∪Finset.univ.biUnion A'
    let D':=P'∪Finset.univ.biUnion A
    D\L=D'\L'∧IsResourceTransformer resources L L' (D\L):=by
  dsimp only
  have hPA:Disjoint P (Finset.univ.biUnion A'):=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hPA' i) he hi
  have hP'A':Disjoint P' (Finset.univ.biUnion A):=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hP'A i) he hi
  have hdec:=resource_decomposition_union resources P _ hP
    (resource_decomposition_biUnion resources A' Finset.univ (fun i _=>hA' i) (fun i _ j _ hij=>hAA' i j hij)) hPA
  have hdec':=resource_decomposition_union resources P' _ hP'
    (resource_decomposition_biUnion resources A Finset.univ (fun i _=>hA i) (fun i _ j _ hij=>hAA i j hij)) hP'A'
  apply resource_transformer_from_disjoint_root_identity resources L L' _ _ hLL hdec hdec'
  intro e
  have hs:(∑ i,if e∈A i then (1:ℤ) else 0)=if e∈Finset.univ.biUnion A then 1 else 0:=by
    have hh:=resource_decomposition_indicator A Finset.univ _ (fun i _ j _ hij=>hAA i j hij) rfl e
    exact_mod_cast hh
  have hs':(∑ i,if e∈A' i then (1:ℤ) else 0)=if e∈Finset.univ.biUnion A' then 1 else 0:=by
    have hh:=resource_decomposition_indicator A' Finset.univ _ (fun i _ j _ hij=>hAA' i j hij) rfl e
    exact_mod_cast hh
  have hUnion (S T:Finset X) (hST:Disjoint S T):
      (if e∈S∪T then (1:ℤ) else 0)=(if e∈S then 1 else 0)+(if e∈T then 1 else 0):=by
    by_cases heS:e∈S <;> by_cases heT:e∈T <;> simp only [Finset.mem_union,heS,heT,or_self,
      or_true,true_or,false_or,or_false,ite_true,ite_false,zero_add,add_zero]
    exact (Finset.disjoint_left.mp hST heS heT).elim
  rw [hUnion _ _ hPA,hUnion _ _ hP'A',←hs,←hs']
  have hi:=hid e
  rw [Finset.sum_sub_distrib] at hi
  linarith only [hi]

end Oberwolfach
