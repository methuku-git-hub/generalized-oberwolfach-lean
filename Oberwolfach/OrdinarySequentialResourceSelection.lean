module

public import Oberwolfach.OrdinaryResourceEndpointSets
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Successive physical-edge selection from a bounded avoidance theorem.
The row and hub costs are charged separately. All original forbidden edges
and all previously selected edges are included in the next forbidden set. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sequential_resource_selection (l f a b:ℕ) (γ:ℝ)
    (W:Finset V) (B:Finset U) (L:Finset (Sym2 V⊕(V×U)))
    (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (hrows:ordinaryResourceRows L⊆W) (hhubs:ordinaryResourceHubs L⊆B)
    (P:Fin l→Finset (Sym2 V⊕(V×U))→Prop)
    (hchoose:∀ (W':Finset V) (B':Finset U) (L':Finset (Sym2 V⊕(V×U))),
      W⊆W'→B⊆B'→W'.card≤f+l*a→(B'.card:ℝ)≤γ+l*b→
      ordinaryResourceRows L'⊆W'→ ordinaryResourceHubs L'⊆B'→
      ∀ i:Fin l,∃ K,P i K∧(ordinaryResourceRows K).card≤a∧
        (ordinaryResourceHubs K).card≤b∧Disjoint K L') :
    ∃ K:Fin l→Finset (Sym2 V⊕(V×U)),
      (∀ i,P i (K i)∧(ordinaryResourceRows (K i)).card≤a∧
        (ordinaryResourceHubs (K i)).card≤b∧Disjoint (K i) L)∧
      (∀ i j,i≠j→Disjoint (K i) (K j))∧
      (ordinaryResourceRows (Finset.univ.biUnion K)).card≤l*a∧
      (ordinaryResourceHubs (Finset.univ.biUnion K)).card≤l*b := by
  let allowed:=fun i K=>P i K∧(ordinaryResourceRows K).card≤a∧
    (ordinaryResourceHubs K).card≤b∧Disjoint K L
  obtain ⟨K,hK,hdis⟩:=sequential_select_prefix l allowed Disjoint ∅ (by
    intro i K hK
    let s:=Finset.univ.filter (fun j:Fin l=>j.val < i.val)
    let used:=s.biUnion K
    let W':=W∪ordinaryResourceRows used
    let B':=B∪ordinaryResourceHubs used
    have hsc:s.card≤l:=by simpa using Finset.card_le_univ s
    have hrow:(ordinaryResourceRows used).card≤l*a:=by
      rw [ordinaryResourceRows_biUnion]
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _j∈s,a := Finset.sum_le_sum (fun j hj=>(hK.2.1 j (Finset.mem_filter.mp hj).2).2.1)
        _ = s.card*a := by simp
        _ ≤ l*a := Nat.mul_le_mul_right _ hsc
    have hhub:(ordinaryResourceHubs used).card≤l*b:=by
      rw [ordinaryResourceHubs_biUnion]
      apply Finset.card_biUnion_le.trans
      calc
        _ ≤ ∑ _j∈s,b := Finset.sum_le_sum (fun j hj=>(hK.2.1 j (Finset.mem_filter.mp hj).2).2.2.1)
        _ = s.card*b := by simp
        _ ≤ l*b := Nat.mul_le_mul_right _ hsc
    have hWc:W'.card≤f+l*a:=
      (Finset.card_union_le _ _).trans (Nat.add_le_add hW hrow)
    have hBc:(B'.card:ℝ)≤γ+l*b:=by
      have hc:(B'.card:ℝ)≤B.card+(ordinaryResourceHubs used).card:=by exact_mod_cast Finset.card_union_le B (ordinaryResourceHubs used)
      have hb':((ordinaryResourceHubs used).card:ℝ)≤l*b:=by exact_mod_cast hhub
      linarith only [hc,hb',hB]
    obtain ⟨C,hC,hCr,hCh,hCd⟩:=hchoose W' B' (L∪used)
      Finset.subset_union_left Finset.subset_union_left hWc hBc
      (by rw [ordinaryResourceRows_union];exact Finset.union_subset_union hrows (fun _ h=>h))
      (by rw [ordinaryResourceHubs_union];exact Finset.union_subset_union hhubs (fun _ h=>h)) i
    refine ⟨C,⟨hC,hCr,hCh,(Finset.disjoint_union_right.mp hCd).1⟩,?_⟩
    intro j hj
    exact ((Finset.disjoint_union_right.mp hCd).2.mono_right
      (Finset.subset_biUnion_of_mem K (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))).symm)
  refine ⟨K,hK,?_,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h|h
    · exact hdis i j h
    · exact (hdis j i h).symm
  · rw [ordinaryResourceRows_biUnion]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _i:Fin l,a := Finset.sum_le_sum (fun i _=>(hK i).2.1)
      _ = l*a := by simp
  · rw [ordinaryResourceHubs_biUnion]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _i:Fin l,b := Finset.sum_le_sum (fun i _=>(hK i).2.2.1)
      _ = l*b := by simp

end Oberwolfach
