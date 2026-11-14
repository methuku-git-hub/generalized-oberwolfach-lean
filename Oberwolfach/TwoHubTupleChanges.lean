module

public import Oberwolfach.FixedDomainTupleChanges
public import Oberwolfach.MarkedCommonCycleTransfers
public import Oberwolfach.MarkedCommonPaths
public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! Common-cycle and common-path losses under changes of their spoke
relations. The fixed rim conditions stay in the base predicate; only free
coordinates are charged, so no root spokes enter the common-path estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem twoHubTuple_spoke_loss (H H' : Bool→V→U→Prop) (u u' : U) (type : I→Bool)
    (base : (I→V)→Prop) (δ : ℝ)
    (hcol : ∀ b u,(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ) :
    (Fintype.card {f : I→V // base f ∧ ∀ i,H (type i) (f i) u ∧ H (type i) (f i) u'}:ℝ)-
      Fintype.card {f : I→V // base f ∧ ∀ i,H' (type i) (f i) u ∧ H' (type i) (f i) u'}≤
      (Fintype.card I:ℝ)*(2*δ)*(Fintype.card V:ℝ)^(Fintype.card I-1) := by
  let D := fun b u=>Finset.univ.filter (fun x=>H b x u ∧ ¬H' b x u)
  have hD (b : Bool) (v : U) : ((D b v).card:ℝ)≤δ := by
    apply le_trans _ (hcol b v)
    simp only [D,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_le_sum
    intro x hx
    by_cases h : H b x v <;> by_cases h' : H' b x v <;> simp [h,h']
  have hUnion (i : I) : (((D (type i) u)∪D (type i) u').card:ℝ)≤2*δ := by
    have hh : (((D (type i) u)∪D (type i) u').card:ℝ)≤(D (type i) u).card+(D (type i) u').card := by
      exact_mod_cast Finset.card_union_le (D (type i) u) (D (type i) u')
    linarith only [hh,hD (type i) u,hD (type i) u']
  have hh := fixedDomainTuple_predicate_loss (Finset.univ : Finset V)
    (fun f : I→V=>base f ∧ ∀ i,H (type i) (f i) u ∧ H (type i) (f i) u')
    (fun f : I→V=>base f ∧ ∀ i,H' (type i) (f i) u ∧ H' (type i) (f i) u')
    (by intros;simp) (by intros;simp) (fun i=>(D (type i) u)∪D (type i) u') (2*δ) hUnion (by
      intro f hf hn
      by_contra hnone
      apply hn
      refine ⟨hf.1,fun i=>?_⟩
      have hnot : f i∉D (type i) u ∧ f i∉D (type i) u' := by
        have hh : f i∉(D (type i) u)∪D (type i) u' := fun he=>hnone ⟨i,he⟩
        simpa only [Finset.mem_union,not_or] using hh
      have h1 := (hf.2 i).1
      have h2 := (hf.2 i).2
      simp only [D,Finset.mem_filter,Finset.mem_univ,true_and,h1,h2,not_not] at hnot
      exact hnot)
  simpa only [Finset.card_univ,Fintype.card_eq_nat_card] using hh

variable {E K : Type*}

theorem rootFirstCommonMarkedPath_spoke_changes
    (tail head : E→V) (ktail khead : K→V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H H' : Bool→V→U→Prop) (j : Bool) (v v' : V) (u u' : U) (δ : ℝ)
    (hcol : ∀ b u,(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ) :
    (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b (H false) (H true) j v v' u u'):ℝ)-
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b (H' false) (H' true) j v v' u u')≤
      2*(m:ℝ)*δ*(Fintype.card V:ℝ)^(m-1) := by
  let base := fun f : Fin m→V=>
    IsRootFirstMarkedCycle tail head ktail khead m π b (if j then Fin.last m else 2) (Fin.cases v f) ∧
    IsRootFirstMarkedCycle tail head ktail khead m π b (if j then Fin.last m else 2) (Fin.cases v' f)
  have he (J : Bool→V→U→Prop) :
      RootFirstCommonMarkedPath tail head ktail khead m π b (J false) (J true) j v v' u u' ≃
      {f : Fin m→V // base f ∧ ∀ i,J (rootFirstSpokeType m j i.succ) (f i) u ∧ J (rootFirstSpokeType m j i.succ) (f i) u'} := by
    apply Equiv.subtypeEquivRight
    intro f
    have hs (i : Fin m) (w : U) :
        (if rootFirstSpokeType m j i.succ then J true (f i) w else J false (f i) w) ↔
          J (rootFirstSpokeType m j i.succ) (f i) w := by cases rootFirstSpokeType m j i.succ <;> simp
    simp only [hs,base,and_assoc]
  rw [Fintype.card_congr (he H),Fintype.card_congr (he H')]
  have hh := twoHubTuple_spoke_loss H H' u u' (fun i : Fin m=>rootFirstSpokeType m j i.succ) base δ hcol
  simp only [Fintype.card_fin] at hh
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  convert hh using 1 <;> ring

theorem commonMarkedCycle_spoke_changes
    (tail head : E→V) (ktail khead : K→V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H H' : Bool→V→U→Prop) (u u' : U) (δ : ℝ)
    (hcol : ∀ b u,(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ) :
    (Fintype.card (CommonMarkedCycle tail head ktail khead m π b (H false) (H true) u u'):ℝ)-
      Fintype.card (CommonMarkedCycle tail head ktail khead m π b (H' false) (H' true) u u')≤
      2*((m:ℝ)+1)*δ*(Fintype.card V:ℝ)^m := by
  let base := IsMarkedCycleTuple tail head ktail khead m π b
  have he (J : Bool→V→U→Prop) :
      CommonMarkedCycle tail head ktail khead m π b (J false) (J true) u u' ≃
      {f : Fin (m+1)→V // base f ∧ ∀ i,J (markedPositionType i) (f i) u ∧ J (markedPositionType i) (f i) u'} := by
    apply (Equiv.subtypeSubtypeEquivSubtypeInter
      (IsMarkedCycleTuple tail head ktail khead m π b)
      (fun C=>MarkedHubCompatible (J false) (J true) C u ∧ MarkedHubCompatible (J false) (J true) C u')).trans
    apply Equiv.subtypeEquivRight
    intro f
    have hs (i : Fin (m+1)) (w : U) :
        (if markedPositionType i then J true (f i) w else J false (f i) w) ↔
          J (markedPositionType i) (f i) w := by cases markedPositionType i <;> simp
    simp only [markedHubCompatible_iff_positions,hs,base,forall_and]
  rw [Fintype.card_congr (he H),Fintype.card_congr (he H')]
  have hh := twoHubTuple_spoke_loss H H' u u' (fun i : Fin (m+1)=>markedPositionType i) base δ hcol
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] at hh
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  convert hh using 1 <;> ring

end Oberwolfach
