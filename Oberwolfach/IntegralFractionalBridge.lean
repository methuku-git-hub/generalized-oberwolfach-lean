module

public import Oberwolfach.FractionalDecompositions
public import Oberwolfach.DecompositionCounts

@[expose] public section

/-! Exact averaging of integral or fractional decompositions. The edge
multiplicity is proved for the actual covering subgraphs before averaging. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem EdgePartition.adjacency_sum {n q : ℕ} {G : SimpleGraph (Fin n)}
    {H : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G H) (u v : Fin n) :
    (∑ i,if (H i).Adj u v then (1:ℝ) else 0)=if G.Adj u v then 1 else 0 := by
  by_cases huv : G.Adj u v
  · obtain ⟨i,hi⟩ := (h u v).1.mp huv
    rw [if_pos huv]
    rw [Finset.sum_eq_single i]
    · simp only [if_pos hi]
    · intro j _ hji
      have hn : ¬(H j).Adj u v := fun hj => hji ((h u v).2 j i hj hi)
      simp only [if_neg hn]
    · simp
  · have hn (i : Fin q) : ¬(H i).Adj u v := fun hi => huv ((h u v).1.mpr ⟨i,hi⟩)
    simp only [if_neg huv,if_neg (hn _),Finset.sum_const_zero]

theorem HasCycleDecomposition.fractional {n r : ℕ} {G : SimpleGraph (Fin n)}
    (h : HasCycleDecomposition G r) : HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r) := by
  obtain ⟨q,H,hpart,hH⟩ := h
  apply fractionalDecomposition_of_indexed G _ H (fun _ => 1)
  · intro i;norm_num
  · intro i _
    exact ⟨hpart.piece_le i,(isEmbeddedCycle_iff_isCycleCopy (H i)).mpr (hH i)⟩
  · exact hpart.adjacency_sum

theorem fractionalDecomposition_of_uniform_cover {V I : Type*}
    [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (H : I → SimpleGraph V)
    (L : ℝ) (hL : 0<L) (hsub : ∀ i,H i≤G)
    (hfrac : ∀ i,HasFractionalDecomposition (H i) P)
    (hcover : ∀ u v,(∑ i,if (H i).Adj u v then (1:ℝ) else 0)=
      if G.Adj u v then L else 0) : HasFractionalDecomposition G P := by
  choose w hw hs he using hfrac
  refine ⟨fun C => (∑ i,w i C)/L,?_,?_,?_⟩
  · intro C;exact div_nonneg (Finset.sum_nonneg (fun i _ => hw i C)) hL.le
  · intro C hC
    have hsum : 0<∑ i,w i C := (div_pos_iff_of_pos_right hL).mp hC
    obtain ⟨i,_,hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i C)).mp hsum
    exact ⟨(hs i C hi).1.trans (hsub i),(hs i C hi).2⟩
  · intro u v
    calc
      (∑ C,if C.Adj u v then (∑ i,w i C)/L else 0)=
          (∑ C,∑ i,if C.Adj u v then w i C else 0)/L := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro C _
        by_cases hc : C.Adj u v <;> simp [hc]
      _ = (∑ i,∑ C,if C.Adj u v then w i C else 0)/L := by rw [Finset.sum_comm]
      _ = (∑ i,if (H i).Adj u v then (1:ℝ) else 0)/L := by simp only [he]
      _ = (if G.Adj u v then L else 0)/L := by rw [hcover]
      _ = if G.Adj u v then 1 else 0 := by split_ifs <;> simp [ne_of_gt hL]

theorem EdgePartition.complement_adjacency_sum {n R : ℕ} {G : SimpleGraph (Fin n)}
    {J : Fin R → SimpleGraph (Fin n)} (h : EdgePartition G J) (u v : Fin n) :
    (∑ i,if (G\J i).Adj u v then (1:ℝ) else 0)=
      if G.Adj u v then (R:ℝ)-1 else 0 := by
  have hi (i : Fin R) : (if (G\J i).Adj u v then (1:ℝ) else 0)=
      (if G.Adj u v then (1:ℝ) else 0)-(if (J i).Adj u v then 1 else 0) := by
    by_cases hg : G.Adj u v
    · by_cases hj : (J i).Adj u v <;> simp [SimpleGraph.sdiff_adj,hg,hj]
    · have hj : ¬(J i).Adj u v := fun hj => hg (h.piece_le i hj)
      simp [SimpleGraph.sdiff_adj,hg,hj]
  simp only [hi,Finset.sum_sub_distrib,h.adjacency_sum]
  split_ifs <;> simp

theorem fractionalDecomposition_of_divisible_complements {n R r : ℕ}
    (G : SimpleGraph (Fin n)) (J : Fin R → SimpleGraph (Fin n))
    (hR : 2≤R) (hpart : EdgePartition G J)
    (hdec : ∀ i,HasCycleDecomposition (G\J i) r) :
    HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r) := by
  apply fractionalDecomposition_of_uniform_cover G _ (fun i => G\J i) ((R:ℝ)-1)
  · have hh : (2:ℝ)≤R := by exact_mod_cast hR
    linarith
  · intro i u v huv;exact huv.1
  · intro i;exact (hdec i).fractional
  · intro u v
    simpa using hpart.complement_adjacency_sum u v

end Oberwolfach
