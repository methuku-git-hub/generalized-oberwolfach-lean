module

public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Exact integer balance under disjoint union and subtraction of a balanced
subgraph. Subtraction uses containment of both the typed arc set and the
actual spoke set; no total-edge congruence is substituted for local balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_filter_union_card {A:Type} [DecidableEq A] (S T:Finset A)
    (h:Disjoint S T) (p:A→Prop) [DecidablePred p]:
    ((S∪T).filter p).card=(S.filter p).card+(T.filter p).card:=by
  rw [Finset.filter_union,Finset.card_union_of_disjoint
    (h.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

theorem finite_filter_sdiff_card {A:Type} [DecidableEq A] (S T:Finset A)
    (h:T⊆S) (p:A→Prop) [DecidablePred p]:
    ((S\T).filter p).card=(S.filter p).card-(T.filter p).card:=by
  have he:(S\T).filter p=S.filter p\T.filter p:=by
    ext a;simp only [Finset.mem_filter,Finset.mem_sdiff];tauto
  rw [he,Finset.card_sdiff_of_subset (Finset.filter_subset_filter p h)]

variable {V U E T:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop} {m:ℕ}

theorem marked_finite_divisible_union (A B:Finset (E⊕T)) (S R:Finset (V×U))
    (hA:Disjoint A B) (hS:Disjoint S R)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (h':MarkedRemainderDivisible tail head ktail khead HK B R m):
    MarkedRemainderDivisible tail head ktail khead HK (A∪B) (S∪R) m:=by
  constructor
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card A B hA,h.directed v,h'.directed v]
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card S R hS,h.row v,h'.row v]
  · intro v
    rw [finite_filter_union_card A B hA,finite_filter_union_card S R hS,h.marked v,h'.marked v]
  · intro u
    rw [finite_filter_union_card S R hS,finite_filter_union_card S R hS,h.hub u,h'.hub u,Nat.mul_add]

theorem marked_finite_divisible_sdiff (A B:Finset (E⊕T)) (S R:Finset (V×U))
    (hA:B⊆A) (hS:R⊆S)
    (h:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (h':MarkedRemainderDivisible tail head ktail khead HK B R m):
    MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m:=by
  constructor
  · intro v
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card A B hA,h.directed v,h'.directed v]
  · intro v
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card S R hS,h.row v,h'.row v]
  · intro v
    rw [finite_filter_sdiff_card A B hA,finite_filter_sdiff_card S R hS,h.marked v,h'.marked v]
  · intro u
    rw [finite_filter_sdiff_card S R hS,finite_filter_sdiff_card S R hS,h.hub u,h'.hub u,Nat.mul_sub_left_distrib]

end Oberwolfach
