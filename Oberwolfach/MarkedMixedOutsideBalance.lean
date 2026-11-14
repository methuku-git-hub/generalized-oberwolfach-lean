module

public import Oberwolfach.MarkedCorrectionOutsideResources

@[expose] public section
/-! Mixed matching components need only satisfy the three vertex-local
balances individually.  Their hub balance is an aggregate condition, so this
lemma does not assign the reference wheel length to each mixed component. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T I:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop}

structure MarkedFiniteLocalBalance (A:Finset (E⊕T)) (S:Finset (V×U)):Prop where
  directed:∀v,(A.filter (fun a=>Sum.elim head khead a=v)).card=
    (A.filter (fun a=>Sum.elim tail ktail a=v)).card
  row:∀v,(A.filter (fun a=>Sum.elim head khead a=v)).card=
    (S.filter (fun s=>s.1=v)).card
  marked:∀v,(A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
    (S.filter (fun s=>s.1=v∧HK s.1 s.2)).card

theorem marked_finite_local_balance_union (A B:Finset (E⊕T)) (S R:Finset (V×U))
    (hA:Disjoint A B) (hS:Disjoint S R)
    (h:MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) A S)
    (h':MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) B R):
    MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) (A∪B) (S∪R) := by
  constructor
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card A B hA,h.directed v,h'.directed v]
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card S R hS,h.row v,h'.row v]
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card S R hS,h.marked v,h'.marked v]

theorem marked_mixed_packing_local_balance
    (M:Finset I) (A:I→Finset (E⊕T)) (S:I→Finset (V×U))
    (hlocal:∀i∈M,MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) (A i) (S i))
    (hA:∀i∈M,∀j∈M,i≠j→Disjoint (A i) (A j))
    (hS:∀i∈M,∀j∈M,i≠j→Disjoint (S i) (S j)):
    MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK)
      (M.biUnion A) (M.biUnion S) := by
  induction M using Finset.induction_on with
  | empty => constructor <;> intro v <;> simp
  | @insert i M hi ih =>
    rw [Finset.biUnion_insert,Finset.biUnion_insert]
    apply marked_finite_local_balance_union
    · apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨j,hj,haj⟩:=Finset.mem_biUnion.mp hb
      exact Finset.disjoint_left.mp (hA i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun hij=>hi (hij ▸ hj))) ha haj
    · apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨j,hj,haj⟩:=Finset.mem_biUnion.mp hb
      exact Finset.disjoint_left.mp (hS i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun hij=>hi (hij ▸ hj))) ha haj
    · exact hlocal i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj=>hlocal j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hne=>hA j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)
        (fun j hj k hk hne=>hS j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne)

theorem marked_mixed_packing_finite_divisible
    (m:ℕ) (M:Finset I) (A:I→Finset (E⊕T)) (S:I→Finset (V×U))
    (hlocal:∀i∈M,MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) (A i) (S i))
    (hA:∀i∈M,∀j∈M,i≠j→Disjoint (A i) (A j))
    (hS:∀i∈M,∀j∈M,i≠j→Disjoint (S i) (S j))
    (hhub:∀u,((M.biUnion S).filter (fun s=>s.2=u∧¬HK s.1 s.2)).card=
      m*((M.biUnion S).filter (fun s=>s.2=u∧HK s.1 s.2)).card):
    MarkedRemainderDivisible tail head ktail khead HK (M.biUnion A) (M.biUnion S) m := by
  obtain ⟨hd,hr,hm⟩:=marked_mixed_packing_local_balance M A S hlocal hA hS
  exact ⟨hd,hr,hm,hhub⟩

theorem marked_correction_outside_after_mixed_matching
    (m:ℕ) (A B C:Finset (E⊕T)) (S R T':Finset (V×U))
    (hA:B⊆A) (hS:R⊆S) (hAC:Disjoint A C) (hST:Disjoint S T')
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK (A∪C) (S∪T') m)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m)
    (M:Finset I) (arc:I→Finset (E⊕T)) (spoke:I→Finset (V×U))
    (hlocal:∀i∈M,MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) (arc i) (spoke i))
    (hArcDis:∀i∈M,∀j∈M,i≠j→Disjoint (arc i) (arc j))
    (hSpokeDis:∀i∈M,∀j∈M,i≠j→Disjoint (spoke i) (spoke j))
    (hArc:M.biUnion arc⊆C) (hSpoke:M.biUnion spoke⊆T')
    (hhub:∀u,((M.biUnion spoke).filter (fun s=>s.2=u∧¬HK s.1 s.2)).card=
      m*((M.biUnion spoke).filter (fun s=>s.2=u∧HK s.1 s.2)).card):
    MarkedRemainderDivisible tail head ktail khead HK
      ((B∪C)\M.biUnion arc) ((R∪T')\M.biUnion spoke) m := by
  have hbase:=marked_correction_with_outside_divisible A B C S R T' hA hS hAC hST hwhole hrest
  have hmatch:=marked_mixed_packing_finite_divisible m M arc spoke hlocal hArcDis hSpokeDis hhub
  exact marked_finite_divisible_sdiff (B∪C) _ (R∪T') _
    (hArc.trans Finset.subset_union_right) (hSpoke.trans Finset.subset_union_right) hbase hmatch
end Oberwolfach
