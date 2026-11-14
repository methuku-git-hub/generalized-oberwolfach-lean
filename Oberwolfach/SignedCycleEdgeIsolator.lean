module

public import Oberwolfach.FractionalCycleIncidence
public import Oberwolfach.GraphSingleEdge
public import Oberwolfach.CycleFractionalThreshold
public import Oberwolfach.FractionalSubgraphs

@[expose] public section

/-! Signed isolation of one physical edge by actual cycle subgraphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem signed_cycle_edge_isolator_of_fractional {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (G : SimpleGraph V) (u v : V) (huv : G.Adj u v)
    (hG : HasFractionalDecomposition G (fun C => IsEmbeddedCycle C r))
    (hD : HasFractionalDecomposition (G\SimpleGraph.edge u v) (fun C => IsEmbeddedCycle C r)) :
    ∃ I : SimpleGraph V → ℝ,
      (∀ C,I C≠0 → C≤G ∧ IsEmbeddedCycle C r) ∧
      (∀ C,|I C|≤1) ∧
      (∀ x y,(∑ C,if C.Adj x y then I C else 0)=
        if (SimpleGraph.edge u v).Adj x y then 1 else 0) ∧
      (∀ x,(∑ C,if C.degree x≠0 then I C else 0)=
        (1/2:ℝ)*(if x=u ∨ x=v then 1 else 0)) := by
  obtain ⟨w,hw,hs,he⟩ := hG
  obtain ⟨w',hw',hs',he'⟩ := hD
  let I (C : SimpleGraph V) := w C-w' C
  have hsub : SimpleGraph.edge u v≤G := (SimpleGraph.edge_le_iff G).mpr (Or.inr huv)
  have hI (C : SimpleGraph V) (hC : I C≠0) : C≤G ∧ IsEmbeddedCycle C r := by
    by_cases hp : 0<w C
    · exact hs C hp
    · have hp' : 0<w' C := by dsimp [I] at hC;rcases ne_iff_lt_or_gt.mp hC with hh|hh <;> linarith [hw C,hw' C]
      exact ⟨(hs' C hp').1.trans sdiff_le,(hs' C hp').2⟩
  have hload (x y : V) : (∑ C,if C.Adj x y then I C else 0)=
      if (SimpleGraph.edge u v).Adj x y then 1 else 0 := by
    calc
      _ = (∑ C,if C.Adj x y then w C else 0)-(∑ C,if C.Adj x y then w' C else 0) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro C _
        dsimp [I]
        split_ifs <;> ring
      _ = _ := by
        rw [he,he']
        by_cases hg : G.Adj x y
        · by_cases hj : (SimpleGraph.edge u v).Adj x y <;> simp [hg,hj,SimpleGraph.sdiff_adj]
        · have hj : ¬(SimpleGraph.edge u v).Adj x y := fun hj => hg (hsub hj)
          simp [hg,hj,SimpleGraph.sdiff_adj]
  refine ⟨I,hI,?_,hload,?_⟩
  · intro C
    have h1 := fractional_cycle_coefficient_le_one G r w hw hs he C
    have h2 := fractional_cycle_coefficient_le_one (G\SimpleGraph.edge u v) r w' hw' hs' he' C
    apply abs_le.mpr
    dsimp [I]
    constructor <;> linarith [hw C,hw' C]
  · intro x
    have hh := signed_cycle_vertex_load r I (fun C hC => (hI C hC).2) x
    have hload' : (∑ y,∑ C,if C.Adj x y then I C else 0)=
        ((SimpleGraph.edge u v).degree x:ℝ) := by
      calc
        _ = ∑ y,if (SimpleGraph.edge u v).Adj x y then (1:ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          exact hload x y
        _ = _ := by
          convert graph_adjacency_row_sum (SimpleGraph.edge u v) x using 1
          · apply Finset.sum_congr rfl
            intro y _
            split_ifs <;> rfl
          · simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    rw [hload'] at hh
    have hd := single_edge_degree u v huv.ne x
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hh hd ⊢
    rw [hd] at hh
    split_ifs at hh ⊢ <;> norm_num at hh ⊢ <;> linarith

theorem signed_cycle_edge_isolator (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ n≥N,∀ G : SimpleGraph (Fin n),
      (∀ x,(cycleThreshold r+α)*(n:ℝ)≤G.degree x) →
      ∀ u v,G.Adj u v →
      ∃ I : SimpleGraph (Fin n) → ℝ,
        (∀ C,I C≠0 → C≤G ∧ IsEmbeddedCycle C r) ∧
        (∀ C,|I C|≤1) ∧
        (∀ x y,(∑ C,if C.Adj x y then I C else 0)=
          if (SimpleGraph.edge u v).Adj x y then 1 else 0) ∧
        (∀ x,(∑ C,if C.degree x≠0 then I C else 0)=
          (1/2:ℝ)*(if x=u ∨ x=v then 1 else 0)) := by
  obtain ⟨N₁,hN₁⟩ := cycle_fractional_positive_margin r hr (α/2) (by positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_constant_le_linear 1 (α/2) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn G hdeg u v huv
  apply signed_cycle_edge_isolator_of_fractional G u v huv
  · apply hN₁ n ((le_max_left _ _).trans hn) G
    intro x
    have ha : 0≤α*(n:ℝ) := mul_nonneg hα.le (Nat.cast_nonneg n)
    nlinarith [hdeg x]
  · apply hN₁ n ((le_max_left _ _).trans hn) (G\SimpleGraph.edge u v)
    intro x
    have hc := congrArg (fun a : ℕ => (a:ℝ)) (single_edge_deletion_degree G u v huv x)
    simp only [Nat.cast_add] at hc
    have hb : ((if x=u ∨ x=v then 1 else 0 : ℕ):ℝ)≤1 := by split_ifs <;> norm_num
    have hn' := hN₂ n ((le_max_right _ _).trans hn)
    have hg := hdeg x
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc hg hn' ⊢
    nlinarith

theorem signed_cycle_edge_isolator_finite (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ G : SimpleGraph V,
      (∀ x,(cycleThreshold r+α)*(Fintype.card V:ℝ)≤G.degree x) →
      ∀ u v,G.Adj u v →
      ∃ I : SimpleGraph V → ℝ,
        (∀ C,I C≠0 → C≤G ∧ IsEmbeddedCycle C r) ∧
        (∀ C,|I C|≤1) ∧
        (∀ x y,(∑ C,if C.Adj x y then I C else 0)=
          if (SimpleGraph.edge u v).Adj x y then 1 else 0) ∧
        (∀ x,(∑ C,if C.degree x≠0 then I C else 0)=
          (1/2:ℝ)*(if x=u ∨ x=v then 1 else 0)) := by
  obtain ⟨N₁,hN₁⟩ := cycle_fractional_positive_margin_finite r hr (α/2) (by positivity)
  obtain ⟨N₂,hN₂⟩ := eventually_constant_le_linear 1 (α/2) (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ hn G hdeg u v huv
  apply signed_cycle_edge_isolator_of_fractional G u v huv
  · apply hN₁ V ((le_max_left _ _).trans hn) G
    intro x
    have ha : 0≤α*(Fintype.card V:ℝ) := mul_nonneg hα.le (Nat.cast_nonneg (Fintype.card V))
    nlinarith [hdeg x]
  · apply hN₁ V ((le_max_left _ _).trans hn) (G\SimpleGraph.edge u v)
    intro x
    have hc := congrArg (fun a : ℕ => (a:ℝ)) (single_edge_deletion_degree G u v huv x)
    simp only [Nat.cast_add] at hc
    have hb : ((if x=u ∨ x=v then 1 else 0 : ℕ):ℝ)≤1 := by split_ifs <;> norm_num
    have hn' := hN₂ (Fintype.card V) ((le_max_right _ _).trans hn)
    have hg := hdeg x
    simp only [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card] at hc hg hn' ⊢
    nlinarith

end Oberwolfach
