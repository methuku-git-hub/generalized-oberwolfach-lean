module

public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Loss between the sum of set sizes and their union, bounded using
actual pair intersections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sum_card_le_union_card_add_pair_bound
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset I) (N : I → Finset V) {B : ℕ}
    (hp : ∀ i∈S,∀ j∈S,i≠j → (N i∩N j).card≤B) :
    (∑ i∈S,(N i).card)≤(S.biUnion N).card+S.card^2*B := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hpS : ∀ j∈S,∀ k∈S,j≠k → (N j∩N k).card≤B :=
      fun j hj k hk hne=>hp j (Finset.mem_insert_of_mem hj) k
        (Finset.mem_insert_of_mem hk) hne
    have hind := ih hpS
    have hint : (N i∩S.biUnion N).card≤S.card*B := by
      have he : N i∩S.biUnion N=S.biUnion (fun j=>N i∩N j) := by
        ext v
        simp only [Finset.mem_inter,Finset.mem_biUnion]
        constructor
        · rintro ⟨hv,j,hj,hvj⟩
          exact ⟨j,hj,hv,hvj⟩
        · rintro ⟨j,hj,hv,hvj⟩
          exact ⟨hv,j,hj,hvj⟩
      rw [he]
      apply Finset.card_biUnion_le_card_mul
      intro j hj
      exact hp i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun he=>hi (he ▸ hj))
    have hcard := Finset.card_union_add_card_inter (N i) (S.biUnion N)
    rw [Finset.sum_insert hi,Finset.biUnion_insert,Finset.card_insert_of_notMem hi]
    calc
      _ ≤ (N i).card+((S.biUnion N).card+S.card^2*B) := Nat.add_le_add_left hind _
      _ = (N i∪S.biUnion N).card+(N i∩S.biUnion N).card+S.card^2*B := by omega
      _ ≤ (N i∪S.biUnion N).card+S.card*B+S.card^2*B := by omega
      _ = (N i∪S.biUnion N).card+(S.card+S.card^2)*B := by ring
      _ ≤ _ := Nat.add_le_add_left
        (Nat.mul_le_mul_right B (by nlinarith : S.card+S.card^2≤(S.card+1)^2)) _

def finiteUnionOverlap {I V : Type*} [DecidableEq V]
    (S : Finset I) (N : I → Finset V) : ℕ :=
  (∑ i∈S,(N i).card)-(S.biUnion N).card

theorem finiteUnionOverlap_add_union {I V : Type*} [DecidableEq V]
    (S : Finset I) (N : I → Finset V) :
    finiteUnionOverlap S N+(S.biUnion N).card=∑ i∈S,(N i).card :=
  Nat.sub_add_cancel Finset.card_biUnion_le

theorem finiteUnionOverlap_le {I V : Type*} [DecidableEq I] [DecidableEq V]
    (S : Finset I) (N : I → Finset V) {B : ℕ}
    (hp : ∀ i∈S,∀ j∈S,i≠j → (N i∩N j).card≤B) :
    finiteUnionOverlap S N≤S.card^2*B := by
  have h := sum_card_le_union_card_add_pair_bound S N hp
  have he := finiteUnionOverlap_add_union S N
  omega

end Oberwolfach
