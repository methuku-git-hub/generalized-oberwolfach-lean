module

public import Oberwolfach.FiniteDisjointChoices
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Simultaneous finite choices with separate row and hub allowances.
Every later choice excludes all earlier row and hub sets, with permutation
separation required only for rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U C:Type} [Fintype I] [DecidableEq I] [DecidableEq V] [DecidableEq U]

theorem finite_separated_row_hub_choices
    (π:Equiv.Perm V) (b:ℕ) (rows:I→C→Finset V) (hubs:I→C→Finset U) (Good:I→C→Prop)
    (R:Finset V) (B:Finset U) (q t:ℕ)
    (hchoose:∀ R':Finset V,∀ B':Finset U,R⊆R'→B⊆B'→
      R'.card≤R.card+Fintype.card I*q→B'.card≤B.card+Fintype.card I*t→∀ i:I,
      ∃ c,Good i c∧(rows i c).card≤q∧(hubs i c).card≤t∧Disjoint (rows i c) R'∧Disjoint (hubs i c) B'∧
        ∀ v∈rows i c,∀ w∈R',¬PermutationClose π b v w):
    ∃ f:I→C,
      (∀ i,Good i (f i)∧(rows i (f i)).card≤q∧(hubs i (f i)).card≤t∧
        Disjoint (rows i (f i)) R∧Disjoint (hubs i (f i)) B∧
        ∀ v∈rows i (f i),∀ w∈R,¬PermutationClose π b v w)∧
      ∀ i j,i≠j→Disjoint (rows i (f i)) (rows j (f j))∧Disjoint (hubs i (f i)) (hubs j (f j))∧
        ∀ v∈rows i (f i),∀ w∈rows j (f j),¬PermutationClose π b v w:=by
  have hinit:∀ i:I,∃ c,Good i c:=by
    intro i
    obtain ⟨c,hc,_⟩:=hchoose R B (by rfl) (by rfl) (by omega) (by omega) i
    exact ⟨c,hc⟩
  choose f₀ hf₀ using hinit
  have hind:∀ T:Finset I,∃ f:I→C,
      (∀ i∈T,Good i (f i)∧(rows i (f i)).card≤q∧(hubs i (f i)).card≤t∧
        Disjoint (rows i (f i)) R∧Disjoint (hubs i (f i)) B∧
        ∀ v∈rows i (f i),∀ w∈R,¬PermutationClose π b v w)∧
      ∀ i∈T,∀ j∈T,i≠j→Disjoint (rows i (f i)) (rows j (f j))∧Disjoint (hubs i (f i)) (hubs j (f j))∧
        ∀ v∈rows i (f i),∀ w∈rows j (f j),¬PermutationClose π b v w:=by
    intro T
    induction T using Finset.induction_on with
    | empty=>exact ⟨f₀,by simp,by simp⟩
    | @insert i T hi ih=>
      obtain ⟨f,hf,hd⟩:=ih
      let R':=R∪T.biUnion (fun j=>rows j (f j))
      let B':=B∪T.biUnion (fun j=>hubs j (f j))
      have hTc:T.card≤Fintype.card I:=Finset.card_le_univ _
      have hr:(T.biUnion (fun j=>rows j (f j))).card≤Fintype.card I*q:=by
        calc
          _ ≤ ∑ j∈T,(rows j (f j)).card:=Finset.card_biUnion_le
          _ ≤ ∑ _j∈T,q:=Finset.sum_le_sum (fun j hj=>(hf j hj).2.1)
          _ = T.card*q:=by simp
          _ ≤ Fintype.card I*q:=Nat.mul_le_mul_right _ hTc
      have hb:(T.biUnion (fun j=>hubs j (f j))).card≤Fintype.card I*t:=by
        calc
          _ ≤ ∑ j∈T,(hubs j (f j)).card:=Finset.card_biUnion_le
          _ ≤ ∑ _j∈T,t:=Finset.sum_le_sum (fun j hj=>(hf j hj).2.2.1)
          _ = T.card*t:=by simp
          _ ≤ Fintype.card I*t:=Nat.mul_le_mul_right _ hTc
      obtain ⟨c,hc,hcq,hct,hcR,hcB,hcsep⟩:=hchoose R' B' Finset.subset_union_left Finset.subset_union_left
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hr _))
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hb _)) i
      have hcr:Disjoint (rows i c) R:=hcR.mono_right Finset.subset_union_left
      have hcb:Disjoint (hubs i c) B:=hcB.mono_right Finset.subset_union_left
      have hcs:∀ v∈rows i c,∀ w∈R,¬PermutationClose π b v w:=fun v hv w hw=>hcsep v hv w (Finset.mem_union_left _ hw)
      have hrj (j:I) (hj:j∈T):rows j (f j)⊆R':=fun v hv=>Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hv⟩)
      have hbj (j:I) (hj:j∈T):hubs j (f j)⊆B':=fun u hu=>Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,hj,hu⟩)
      have hcj (j:I) (hj:j∈T):Disjoint (rows i c) (rows j (f j))∧Disjoint (hubs i c) (hubs j (f j))∧
          ∀ v∈rows i c,∀ w∈rows j (f j),¬PermutationClose π b v w:=
        ⟨hcR.mono_right (hrj j hj),hcB.mono_right (hbj j hj),fun v hv w hw=>hcsep v hv w (hrj j hj hw)⟩
      have hjc (j:I) (hj:j∈T):Disjoint (rows j (f j)) (rows i c)∧Disjoint (hubs j (f j)) (hubs i c)∧
          ∀ v∈rows j (f j),∀ w∈rows i c,¬PermutationClose π b v w:=
        ⟨(hcj j hj).1.symm,(hcj j hj).2.1.symm,
          fun v hv w hw hh=>(hcj j hj).2.2 w hw v hv ((permutationClose_symm π b _ _).mp hh)⟩
      refine ⟨Function.update f i c,?_,?_⟩
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl|hj
        · simpa only [Function.update_self] using And.intro hc (And.intro hcq (And.intro hct (And.intro hcr (And.intro hcb hcs))))
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
            simpa only [Function.update_self,Function.update_of_ne hji] using hjc j hjT
          · have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
            simpa only [Function.update_of_ne hji,Function.update_of_ne hki] using hd j hjT k hkT hjk
  obtain ⟨f,hf,hd⟩:=hind Finset.univ
  exact ⟨f,fun i=>hf i (Finset.mem_univ _),fun i j=>hd i (Finset.mem_univ _) j (Finset.mem_univ _)⟩

end Oberwolfach
