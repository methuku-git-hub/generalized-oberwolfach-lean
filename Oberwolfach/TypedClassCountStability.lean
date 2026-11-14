module

public import Oberwolfach.TypedCycleClassLoads
public import Oberwolfach.FixedDomainTupleChanges
public import Oberwolfach.TwoHubTupleChanges

@[expose] public section

/-! Counts after changing the two fixed classes. Each lost tuple is charged
to one of its free coordinates. No root membership is tested for paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

 theorem typed_class_tuple_loss (A B A' B':Finset V) (j:I→Bool) (base:(I→V)→Prop):
    (Fintype.card {f:I→V // base f∧∀ i,if j i then f i∈A else f i∈B}:ℝ)-
      Fintype.card {f:I→V // base f∧∀ i,if j i then f i∈A' else f i∈B'}≤
      (Fintype.card I:ℝ)*((changed A A').card+(changed B B').card)*(Fintype.card V:ℝ)^(Fintype.card I-1):=by
  let D:I→Finset V:=fun i=>if j i then A\A' else B\B'
  have hD:∀ i,((D i).card:ℝ)≤((changed A A').card:ℝ)+(changed B B').card:=by
    intro i
    have hA:(A\A').card≤(changed A A').card:=by
      apply Finset.card_le_card
      intro x hx
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff] using Or.inl (Finset.mem_sdiff.mp hx)
    have hB:(B\B').card≤(changed B B').card:=by
      apply Finset.card_le_card
      intro x hx
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff] using Or.inl (Finset.mem_sdiff.mp hx)
    cases hj:j i <;> dsimp [D] <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true]
    · exact_mod_cast hB.trans (Nat.le_add_left _ _)
    · exact_mod_cast hA.trans (Nat.le_add_right _ _)
  have hh:=fixedDomainTuple_predicate_loss (Finset.univ:Finset V)
    (fun f:I→V=>base f∧∀ i,if j i then f i∈A else f i∈B)
    (fun f:I→V=>base f∧∀ i,if j i then f i∈A' else f i∈B')
    (by intros;simp) (by intros;simp) D
    (((changed A A').card:ℝ)+(changed B B').card) hD (by
      intro f hf hn
      by_contra hnone
      apply hn
      refine ⟨hf.1,fun i=>?_⟩
      have hd:f i∉D i:=fun h=>hnone ⟨i,h⟩
      have hh:=hf.2 i
      cases hj:j i <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
      · by_contra h
        exact hd (by simpa only [D,hj,Bool.false_eq_true,ite_false] using Finset.mem_sdiff.mpr ⟨hh,h⟩)
      · by_contra h
        exact hd (by simpa only [D,hj,ite_true] using Finset.mem_sdiff.mpr ⟨hh,h⟩))
  simpa only [Finset.card_univ,Fintype.card_eq_nat_card,Nat.card_fin] using hh

variable {E K:Type}

 theorem class_marked_cycle_count_change (tail head:E→V) (ktail khead:K→V)
    (m:ℕ) (π:Equiv.Perm V) (b:ℕ) (A B A' B':Finset V):
    (Fintype.card (ClassMarkedCycle tail head ktail khead m π b A B):ℝ)-
      Fintype.card (ClassMarkedCycle tail head ktail khead m π b A' B')≤
      (m+1:ℝ)*((changed A A').card+(changed B B').card)*(Fintype.card V:ℝ)^m:=by
  have he (A B:Finset V):ClassMarkedCycle tail head ktail khead m π b A B≃
      {f:Fin (m+1)→V // IsMarkedCycleTuple tail head ktail khead m π b f∧
        ∀ i,if markedPositionType i then f i∈A else f i∈B}:=by
    apply Equiv.subtypeEquivRight
    intro f
    rw [markedHubCompatible_iff_positions]
  rw [Fintype.card_congr (he A B),Fintype.card_congr (he A' B')]
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,Fintype.card_eq_nat_card,Nat.card_fin] using
    typed_class_tuple_loss A B A' B' markedPositionType (IsMarkedCycleTuple tail head ktail khead m π b)

 theorem class_marked_path_count_change (tail head:E→V) (ktail khead:K→V)
    (m:ℕ) (π:Equiv.Perm V) (b:ℕ) (A B A' B':Finset V) (j:Bool) (v v':V):
    (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
      (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ()):ℝ)-
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B') (fun x (_:Unit)=>x∈A') j v v' () ())≤
      (m:ℝ)*((changed A A').card+(changed B B').card)*(Fintype.card V:ℝ)^(m-1):=by
  let base:=fun f:Fin m→V=>
    IsRootFirstMarkedCycle tail head ktail khead m π b (if j then Fin.last m else 2) (Fin.cases v f)∧
    IsRootFirstMarkedCycle tail head ktail khead m π b (if j then Fin.last m else 2) (Fin.cases v' f)
  have he (A B:Finset V):RootFirstCommonMarkedPath tail head ktail khead m π b
      (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ()≃
      {f:Fin m→V // base f∧∀ i,if rootFirstSpokeType m j i.succ then f i∈A else f i∈B}:=by
    apply Equiv.subtypeEquivRight
    intro f
    simp only [base,and_self,and_assoc]
  rw [Fintype.card_congr (he A B),Fintype.card_congr (he A' B')]
  simpa only [Fintype.card_fin,Fintype.card_eq_nat_card,Nat.card_fin] using typed_class_tuple_loss A B A' B'
    (fun i:Fin m=>rootFirstSpokeType m j i.succ) base

end Oberwolfach
