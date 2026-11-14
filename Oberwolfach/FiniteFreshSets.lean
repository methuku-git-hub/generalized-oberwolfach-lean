module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section
/-! Choosing finitely many equal-sized sets while excluding all earlier sets. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_fresh_sets {J V:Type} [Fintype J] [DecidableEq J] [DecidableEq V]
    (s:ℕ) (P:J→Finset V→Prop)
    (hchoose:∀ i (B:Finset V),B.card≤Fintype.card J*s →
      ∃ S:Finset V,S.card=s ∧ P i S ∧ Disjoint S B):
    ∃ S:J→Finset V,(∀ i,(S i).card=s∧P i (S i)) ∧
      ∀ i j,i≠j→Disjoint (S i) (S j) := by
  have hstep:∀ T:Finset J,∃ S:J→Finset V,
      (∀ i∈T,(S i).card=s∧P i (S i)) ∧
      ∀ i∈T,∀ j∈T,i≠j→Disjoint (S i) (S j):=by
    intro T
    induction T using Finset.induction with
    | empty=>
      refine ⟨fun _=>∅,?_,?_⟩ <;> simp
    | @insert i T hi ih=>
      obtain ⟨S,hS,hdis⟩:=ih
      let B:=T.biUnion S
      have hB:B.card≤Fintype.card J*s:=by
        calc
          _ ≤ T.card*s:=Finset.card_biUnion_le_card_mul T S s (by intro j hj; exact (hS j hj).1.le)
          _ ≤ Fintype.card J*s:=Nat.mul_le_mul_right s (Finset.card_le_univ T)
      obtain ⟨A,hA,hP,hAB⟩:=hchoose i B hB
      let S':=Function.update S i A
      refine ⟨S',?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · simpa [S'] using And.intro hA hP
        · have hji:j≠i:=by intro he;subst j;exact hi hj
          simpa [S',Function.update_of_ne hji] using hS j hj
      · intro j hj k hk hjk
        by_cases hji:j=i
        · subst j
          have hki:k≠i:=hjk.symm
          have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
          have hkB:S k⊆B:=by intro v hv;exact Finset.mem_biUnion.mpr ⟨k,hkT,hv⟩
          simpa [S',Function.update_of_ne hki] using hAB.mono_right hkB
        · have hjT:j∈T:=(Finset.mem_insert.mp hj).resolve_left hji
          by_cases hki:k=i
          · subst k
            have hjB:S j⊆B:=by intro v hv;exact Finset.mem_biUnion.mpr ⟨j,hjT,hv⟩
            simpa [S',Function.update_of_ne hji] using (hAB.mono_right hjB).symm
          · have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
            simpa [S',Function.update_of_ne hji,Function.update_of_ne hki] using hdis j hjT k hkT hjk

  obtain ⟨S,hS,hdis⟩:=hstep Finset.univ
  exact ⟨S,fun i=>hS i (Finset.mem_univ i),fun i j=>hdis i (Finset.mem_univ i) j (Finset.mem_univ j)⟩
end Oberwolfach
