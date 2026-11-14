module

public import Oberwolfach.MarkedFiniteDivisibilityOperations

@[expose] public section
/-! Exact signed hub discrepancy for a mixed deletion.  No assertion that
individual variable-length components have the reference ratio is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [DecidableEq V] [DecidableEq U]

def markedFiniteHubDiscrepancy (HK:V→U→Prop) (m:ℕ) (S:Finset (V×U)) (u:U):ℤ :=
  ((S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:ℤ) -
    (m:ℤ)*((S.filter (fun s=>s.2=u∧HK s.1 s.2)).card:ℤ)

theorem marked_finite_hub_discrepancy_sdiff
    (HK:V→U→Prop) (m:ℕ) (S R:Finset (V×U)) (hR:R⊆S) (u:U):
    markedFiniteHubDiscrepancy HK m S u =
      markedFiniteHubDiscrepancy HK m (S\R) u + markedFiniteHubDiscrepancy HK m R u := by
  have hunion:S=(S\R)∪R := by
    ext s
    have hs:s∈R→s∈S:=fun h=>hR h
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  have hdis:Disjoint (S\R) R := by
    apply Finset.disjoint_left.mpr
    intro s hs hr
    exact (Finset.mem_sdiff.mp hs).2 hr
  have hno:((S.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:ℤ)=
      (((S\R).filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:ℤ)+
      ((R.filter (fun s=>s.2=u∧¬HK s.1 s.2)).card:ℤ) := by
    conv_lhs => rw [hunion]
    rw [finite_filter_union_card _ _ hdis, Nat.cast_add]
  have hyes:((S.filter (fun s=>s.2=u∧HK s.1 s.2)).card:ℤ)=
      (((S\R).filter (fun s=>s.2=u∧HK s.1 s.2)).card:ℤ)+
      ((R.filter (fun s=>s.2=u∧HK s.1 s.2)).card:ℤ) := by
    conv_lhs => rw [hunion]
    rw [finite_filter_union_card _ _ hdis, Nat.cast_add]
  unfold markedFiniteHubDiscrepancy
  rw [hno,hyes]
  ring

theorem marked_finite_hub_discrepancy_of_divisible
    {E T:Type} [DecidableEq E] [DecidableEq T]
    (tail head:E→V) (ktail khead:T→V) (HK:V→U→Prop) (m:ℕ)
    (A:Finset (E⊕T)) (S:Finset (V×U))
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m) (u:U):
    markedFiniteHubDiscrepancy HK m S u=0 := by
  unfold markedFiniteHubDiscrepancy
  have hh:=h.hub u
  exact sub_eq_zero.mpr (by exact_mod_cast hh)

theorem marked_finite_hub_discrepancy_biUnion
    {I:Type} [DecidableEq I] (HK:V→U→Prop) (m:ℕ) (M:Finset I)
    (S:I→Finset (V×U))
    (hdis:∀i∈M,∀j∈M,i≠j→Disjoint (S i) (S j)) (u:U):
    markedFiniteHubDiscrepancy HK m (M.biUnion S) u =
      ∑i∈M,markedFiniteHubDiscrepancy HK m (S i) u := by
  induction M using Finset.induction_on with
  | empty => simp [markedFiniteHubDiscrepancy]
  | @insert i M hi ih =>
    have hd:Disjoint (S i) (M.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨j,hj,hxj⟩:=Finset.mem_biUnion.mp hx'
      exact Finset.disjoint_left.mp (hdis i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun hij=>hi (hij ▸ hj))) hx hxj
    rw [Finset.biUnion_insert,Finset.sum_insert hi]
    have he:markedFiniteHubDiscrepancy HK m (S i∪M.biUnion S) u=
        markedFiniteHubDiscrepancy HK m (S i) u +
          markedFiniteHubDiscrepancy HK m (M.biUnion S) u := by
      unfold markedFiniteHubDiscrepancy
      rw [finite_filter_union_card _ _ hd,finite_filter_union_card _ _ hd]
      push_cast
      ring
    rw [he,ih (fun j hj k hk hne=>hdis j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)]

theorem marked_finite_balanced_remainder_hub_discrepancy
    {E T:Type} [DecidableEq E] [DecidableEq T]
    (tail head:E→V) (ktail khead:T→V) (HK:V→U→Prop) (m:ℕ)
    (A:Finset (E⊕T)) (S R:Finset (V×U)) (hR:R⊆S)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m) (u:U):
    markedFiniteHubDiscrepancy HK m (S\R) u = -markedFiniteHubDiscrepancy HK m R u := by
  have he:=marked_finite_hub_discrepancy_sdiff HK m S R hR u
  have hz:=marked_finite_hub_discrepancy_of_divisible tail head ktail khead HK m A S h u
  omega

end Oberwolfach
