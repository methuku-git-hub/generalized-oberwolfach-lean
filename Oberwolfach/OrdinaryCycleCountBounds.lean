module

public import Oberwolfach.FractionalCycleIncidence
public import Oberwolfach.MarkedCycleCountBounds

@[expose] public section

/-! Counting actual cycle subgraphs through a fixed physical edge. A chosen
embedding is only used as an injective encoding; it does not give multiplicity
to cycles in any fractional weighting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev EmbeddedCycleFamily (V : Type*) (r : ℕ) :=
  {C : SimpleGraph V // IsEmbeddedCycle C r}

def embeddedCycleEmbedding {V : Type*} {r : ℕ} (C : EmbeddedCycleFamily V r) : Fin r ↪ V :=
  Classical.choose C.property.2

theorem embeddedCycleEmbedding_spec {V : Type*} {r : ℕ} (C : EmbeddedCycleFamily V r) :
    C.val=(SimpleGraph.cycleGraph r).map (embeddedCycleEmbedding C) :=
  Classical.choose_spec C.property.2

theorem embeddedCycleEmbedding_injective {V : Type*} {r : ℕ} :
    Function.Injective (fun C : EmbeddedCycleFamily V r => (embeddedCycleEmbedding C : Fin r → V)) := by
  intro C D h
  apply Subtype.ext
  change (embeddedCycleEmbedding C : Fin r → V)=(embeddedCycleEmbedding D : Fin r → V) at h
  rw [embeddedCycleEmbedding_spec C,embeddedCycleEmbedding_spec D,h]

theorem finite_injective_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (f : I → J) (hf : Function.Injective f) (g : J → ℝ) (hg : ∀ j,0≤g j) :
    (∑ i,g (f i))≤∑ j,g j := by
  classical
  calc
    _ = ∑ j∈Finset.univ.image f,g j := by rw [Finset.sum_image];exact fun i _ j _ hij => hf hij
    _ ≤ ∑ j,g j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hg j)

theorem ordinary_cycle_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (r : ℕ) (u v : V) (huv : u≠v) :
    (∑ C : EmbeddedCycleFamily V r,if C.val.Adj u v then (1:ℝ) else 0)≤
      (r:ℝ)^2*(Fintype.card V:ℝ)^(r-2) := by
  let g (f : Fin r → V) := ∑ i,∑ j,if i≠j ∧ f i=u ∧ f j=v then (1:ℝ) else 0
  have hg (f : Fin r → V) : 0≤g f := by
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hC (C : EmbeddedCycleFamily V r) : (if C.val.Adj u v then (1:ℝ) else 0)≤g (embeddedCycleEmbedding C) := by
    by_cases hadj : C.val.Adj u v
    · rw [if_pos hadj]
      have hh := hadj
      rw [embeddedCycleEmbedding_spec C,SimpleGraph.map_adj] at hh
      obtain ⟨i,j,hij,hi,hj⟩ := hh
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

theorem IsEmbeddedCycle.support_card {V : Type*} [Fintype V] [DecidableEq V]
    {C : SimpleGraph V} {r : ℕ} (hC : IsEmbeddedCycle C r) : C.support.toFinset.card=r := by
  obtain ⟨hr,f,rfl⟩ := hC
  have hs : (SimpleGraph.cycleGraph r).support=Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    have hh := ((SimpleGraph.cycleGraph r).degree_eq_zero_iff_notMem_support i).mpr hi
    have hd := cycleGraph_regular hr i
    simp only [← SimpleGraph.ncard_neighborSet] at hh hd
    omega
  rw [← Set.ncard_coe_finset,Set.coe_toFinset,SimpleGraph.support_map,
    Set.ncard_image_of_injective _ f.injective,hs]
  simp

end Oberwolfach
