module

public import Oberwolfach.FiniteDisjointChoices
public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
 theorem finite_conflict_separated_choices {I V C:Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    (S:C→Finset V) (Good:I→C→Prop) (W:Finset V) (d:ℕ)
    (F:SimpleGraph V) (L:ℝ) (hL:0≤L) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hchoose:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*d*(L+1)→
      ∃ c,Good i c ∧ (S c).card≤d ∧ Disjoint (S c) B):
    ∃ f:I→C,(∀ i,Good i (f i) ∧ (S (f i)).card≤d ∧ Disjoint (S (f i)) W) ∧
      ∀ i j,i≠j→Disjoint (S (f i)) (S (f j)) ∧
      (∀ v∈S (f i),∀ w∈S (f j),¬F.Adj v w):=by
  have hinit:∀ i,∃ c,Good i c:=by
    intro i
    obtain ⟨c,hc,_,_⟩:=hchoose i W (le_add_of_nonneg_right (by positivity))
    exact ⟨c,hc⟩
  choose f₀ hf₀ using hinit
  have hind:∀ T:Finset I,∃ f:I→C,
      (∀ i∈T,Good i (f i) ∧ (S (f i)).card≤d ∧ Disjoint (S (f i)) W) ∧
      (∀ i∈T,∀ j∈T,i≠j→Disjoint (S (f i)) (S (f j)) ∧
        (∀ v∈S (f i),∀ w∈S (f j),¬F.Adj v w)):=by
    intro T
    induction T using Finset.induction_on with
    | empty=>exact ⟨f₀,by simp,by simp⟩
    | @insert i T hi ih=>
      obtain ⟨f,hf,hdis⟩:=ih
      let T₀:=T.biUnion (fun j=>S (f j))
      let B:=W∪(T₀∪T₀.biUnion (fun v=>F.neighborFinset v))
      have hB:(B.card:ℝ)≤W.card+Fintype.card I*d*(L+1):=by
        have hh:T₀.card≤T.card*d:=by
          calc
            _ ≤ ∑ j∈T,(S (f j)).card:=Finset.card_biUnion_le
            _ ≤ ∑ _j∈T,d:=Finset.sum_le_sum (fun j hj=>(hf j hj).2.1)
            _ = T.card*d:=by simp
        have ht:T.card≤Fintype.card I:=Finset.card_le_univ _
        have h0:(T₀.card:ℝ)≤Fintype.card I*d:=by
          exact_mod_cast hh.trans (Nat.mul_le_mul_right d ht)
        have h1:=forbidden_used_neighbours_card F T₀ L hF
        have hu:(B.card:ℝ)≤W.card+(T₀∪T₀.biUnion (fun v=>F.neighborFinset v)).card:=by
          exact_mod_cast Finset.card_union_le W (T₀∪T₀.biUnion (fun v=>F.neighborFinset v))
        have h2:=mul_le_mul_of_nonneg_right h0 (show 0≤L+1 by linarith)
        linarith only [h1,hu,h2]
      obtain ⟨c,hc,hcd,hcB⟩:=hchoose i B hB
      have hcW:Disjoint (S c) W:=hcB.mono_right Finset.subset_union_left
      have hcj (j:I) (hj:j∈T):Disjoint (S c) (S (f j)) ∧
          (∀ v∈S c,∀ w∈S (f j),¬F.Adj v w):=by
        constructor
        · apply hcB.mono_right
          intro v hv
          exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j,hj,hv⟩))
        · intro v hv w hw h
          apply Finset.disjoint_left.mp hcB hv
          exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨w,Finset.mem_biUnion.mpr ⟨j,hj,hw⟩,
              (F.mem_neighborFinset w v).mpr h.symm⟩))
      have hjc (j:I) (hj:j∈T):Disjoint (S (f j)) (S c) ∧
          (∀ v∈S (f j),∀ w∈S c,¬F.Adj v w):=
        ⟨(hcj j hj).1.symm,fun v hv w hw h=>(hcj j hj).2 w hw v hv h.symm⟩
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
            simpa only [Function.update_self,Function.update_of_ne hji] using hjc j hjT
          · have hkT:k∈T:=(Finset.mem_insert.mp hk).resolve_left hki
            simpa only [Function.update_of_ne hji,Function.update_of_ne hki] using hdis j hjT k hkT hjk
  obtain ⟨f,hf,hd⟩:=hind Finset.univ
  exact ⟨f,fun i=>hf i (Finset.mem_univ _),fun i j=>hd i (Finset.mem_univ _) j (Finset.mem_univ _)⟩

end Oberwolfach
