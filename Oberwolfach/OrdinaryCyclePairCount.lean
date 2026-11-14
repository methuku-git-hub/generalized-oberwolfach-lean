module

public import Oberwolfach.OrdinaryCycleCountBounds

@[expose] public section
/-! Counting cycle subgraphs through two vertices, whether adjacent or not. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_two_vertex_count {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (u v : V) (huv : u≠v) :
    (∑ C : EmbeddedCycleFamily V r,
      if u∈Set.range (embeddedCycleEmbedding C) ∧ v∈Set.range (embeddedCycleEmbedding C) then (1:ℝ) else 0)≤
      (r:ℝ)^2*(Fintype.card V:ℝ)^(r-2) := by
  let g (f : Fin r → V) := ∑ i,∑ j,if i≠j ∧ f i=u ∧ f j=v then (1:ℝ) else 0
  have hg (f : Fin r → V) : 0≤g f := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hC (C : EmbeddedCycleFamily V r) : (if u∈Set.range (embeddedCycleEmbedding C) ∧ v∈Set.range (embeddedCycleEmbedding C) then (1:ℝ) else 0)≤g (embeddedCycleEmbedding C) := by
    by_cases hadj : u∈Set.range (embeddedCycleEmbedding C) ∧ v∈Set.range (embeddedCycleEmbedding C)
    · rw [if_pos hadj]
      obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩ := hadj
      have hne : i≠j := by intro he;apply huv;rw [← hi,← hj,he]
      have hjSum := Finset.single_le_sum (s:=Finset.univ)
        (f:=fun j => if i≠j ∧ embeddedCycleEmbedding C i=u ∧ embeddedCycleEmbedding C j=v then (1:ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ j)
      have hc : i≠j ∧ embeddedCycleEmbedding C i=u ∧ embeddedCycleEmbedding C j=v := ⟨hne,hi,hj⟩
      rw [if_pos hc] at hjSum
      apply hjSum.trans
      dsimp only [g]
      exact Finset.single_le_sum (f:=fun i : Fin r => ∑ j : Fin r,
        if i≠j ∧ embeddedCycleEmbedding C i=u ∧ embeddedCycleEmbedding C j=v then (1:ℝ) else 0)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)) (Finset.mem_univ i)
    · simp only [if_neg hadj]
      exact hg _
  calc
    _ ≤ ∑ C : EmbeddedCycleFamily V r,g (embeddedCycleEmbedding C) := Finset.sum_le_sum (fun C _ => hC C)
    _ ≤ ∑ f : Fin r → V,g f := finite_injective_sum_le _ embeddedCycleEmbedding_injective g hg
    _ = ∑ i : Fin r,∑ j : Fin r,∑ f : Fin r → V,
        if i≠j ∧ f i=u ∧ f j=v then (1:ℝ) else 0 := by
      dsimp [g]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ ≤ ∑ _i : Fin r,∑ _j : Fin r,(Fintype.card V:ℝ)^(r-2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i=j
      · simp only [hij,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
        positivity
      · have hh := two_position_indicator_total i j hij u v
        simp only [Fintype.card_fin] at hh
        simp only [hij,ne_eq,not_false_eq_true,true_and]
        convert hh.le using 1
        apply Finset.sum_congr rfl
        intro f _
        split_ifs <;> rfl
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring


theorem embedded_cycle_support_range {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (C:EmbeddedCycleFamily V r) :
    C.val.support = Set.range (embeddedCycleEmbedding C) := by
  have hr:3≤r:=C.property.1
  have hs:(SimpleGraph.cycleGraph r).support=Set.univ:=by
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    have hh:=((SimpleGraph.cycleGraph r).degree_eq_zero_iff_notMem_support i).mpr hi
    have hd:=cycleGraph_regular hr i
    simp only [← SimpleGraph.ncard_neighborSet] at hh hd
    omega
  rw [embeddedCycleEmbedding_spec C,SimpleGraph.support_map,hs]
  exact Set.image_univ
end Oberwolfach
