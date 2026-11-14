module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-! Sequential finite choices with the exact accumulated vertex budget.
The extension premise is applied to the union of the previously chosen
supports and the original forbidden set. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

 theorem finite_disjoint_choices {I V C:Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (S:C→Finset V) (Good:I→C→Prop) (W:Finset V) (d:ℕ)
    (hchoose:∀ i,∀ B:Finset V,B.card≤W.card+Fintype.card I*d→
      ∃ c,Good i c ∧ (S c).card≤d ∧ Disjoint (S c) B):
    ∃ f:I→C,(∀ i,Good i (f i) ∧ (S (f i)).card≤d ∧ Disjoint (S (f i)) W) ∧
      ∀ i j,i≠j→Disjoint (S (f i)) (S (f j)):=by
  have hinit:∀ i,∃ c,Good i c:=by
    intro i
    obtain ⟨c,hc,_,_⟩:=hchoose i W (by omega)
    exact ⟨c,hc⟩
  choose f₀ hf₀ using hinit
  have hind:∀ T:Finset I,∃ f:I→C,
      (∀ i∈T,Good i (f i) ∧ (S (f i)).card≤d ∧ Disjoint (S (f i)) W) ∧
      (∀ i∈T,∀ j∈T,i≠j→Disjoint (S (f i)) (S (f j))):=by
    intro T
    induction T using Finset.induction_on with
    | empty=>exact ⟨f₀,by simp,by simp⟩
    | @insert i T hi ih=>
      obtain ⟨f,hf,hdis⟩:=ih
      let B:=W∪T.biUnion (fun j=>S (f j))
      have hB:B.card≤W.card+Fintype.card I*d:=by
        have hh:(T.biUnion (fun j=>S (f j))).card≤T.card*d:=by
          calc
            _ ≤ ∑ j∈T,(S (f j)).card:=Finset.card_biUnion_le
            _ ≤ ∑ _j∈T,d:=Finset.sum_le_sum (fun j hj=>(hf j hj).2.1)
            _ = T.card*d:=by simp
        have ht:T.card≤Fintype.card I:=Finset.card_le_univ _
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
          (hh.trans (Nat.mul_le_mul_right d ht)) _)
      obtain ⟨c,hc,hcd,hcB⟩:=hchoose i B hB
      have hcW:Disjoint (S c) W:=hcB.mono_right Finset.subset_union_left
      have hcj (j:I) (hj:j∈T):Disjoint (S c) (S (f j)):=by
        apply hcB.mono_right
        intro v hv
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hv⟩)
      refine ⟨Function.update f i c,?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · simpa only [Function.update_self] using And.intro hc (And.intro hcd hcW)
        · have hji:j≠i:=fun he=>hi (he ▸ hj)
          simpa only [Function.update_of_ne hji] using hf j hj
      · intro j hj k hk hjk
        by_cases hji:j=i
        · subst j
          have hki:k≠i:=Ne.symm hjk
          have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
          simpa only [Function.update_self,Function.update_of_ne hki] using hcj k hkT
        · have hjT:j∈T:=(Finset.mem_insert.mp hj).resolve_left hji
          by_cases hki:k=i
          · subst k
            simpa only [Function.update_self,Function.update_of_ne hji] using (hcj j hjT).symm
          · have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
            simpa only [Function.update_of_ne hji,Function.update_of_ne hki] using hdis j hjT k hkT hjk
  obtain ⟨f,hf,hd⟩:=hind Finset.univ
  exact ⟨f,fun i=>hf i (Finset.mem_univ _),fun i j=>hd i (Finset.mem_univ _) j (Finset.mem_univ _)⟩

end Oberwolfach
