module

public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Repeated single-copy existence after bounded deletion supplies the
edge-disjoint candidate families required by the selection lemma. The
budget includes every previously chosen candidate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sequential_select_prefix {C : Type*} (N : ℕ)
    (allowed : Fin N → C → Prop) (compatible : C → C → Prop) (empty : C)
    (hchoice : ∀ i : Fin N, ∀ F, SelectionPrefix allowed compatible empty i.val F →
      ∃ c, allowed i c ∧ ∀ j, j.val < i.val → compatible (F j) c) :
    ∃ F : Fin N → C, (∀ i, allowed i (F i)) ∧
      ∀ i j, i.val < j.val → compatible (F i) (F j) := by
  have hprefix : ∀ k : ℕ, k ≤ N → ∃ F, SelectionPrefix allowed compatible empty k F := by
    intro k
    induction k with
    | zero => intro _; exact ⟨fun _ => empty, selectionPrefix_zero allowed compatible empty⟩
    | succ k ih =>
      intro hk
      obtain ⟨F, hF⟩ := ih (by omega)
      let i : Fin N := ⟨k, by omega⟩
      obtain ⟨c, hc, hcomp⟩ := hchoice i F hF
      exact ⟨Function.update F i c, selectionPrefix_update allowed compatible empty i F c hF hc hcomp⟩
  obtain ⟨F, hF⟩ := hprefix N le_rfl
  exact ⟨F, fun i => hF.2.1 i i.isLt, fun i j hij => hF.2.2 i j hij j.isLt⟩

theorem graph_degree_sup_le {V : Type*} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (v : V) : (G ⊔ H).degree v ≤ G.degree v + H.degree v := by
  simpa only [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup]
    using Finset.card_union_le (G.neighborFinset v) (H.neighborFinset v)

theorem graph_iSup_prefix_degree_bound {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (F : Fin t → SimpleGraph V) (i : Fin t) (D : ℕ)
    (hD : ∀ j v, (F j).degree v ≤ D)
    (hfuture : ∀ j, i.val ≤ j.val → F j = ⊥) (v : V) :
    (⨆ j, F j).degree v ≤ D * i.val := by
  have hh := graph_iSup_local_degree_bound F Finset.univ v D (fun j => hD j v)
  simp only [Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree] at hh
  have hcard : (Finset.univ.filter (fun j => ∃ w ∈ (Finset.univ : Finset V), (F j).Adj v w)).card ≤ i.val := by
    have hsub : (Finset.univ.filter (fun j => ∃ w ∈ (Finset.univ : Finset V), (F j).Adj v w)) ⊆
        Finset.univ.filter (fun j => j.val < i.val) := by
      intro j hj
      obtain ⟨w, _, hw⟩ := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      by_contra hn
      rw [hfuture j (by omega)] at hw
      exact hw.elim
    have hc : (Finset.univ.filter (fun j : Fin t => j.val < i.val)).card = i.val := by
      simpa only [min_eq_right (Nat.le_of_lt i.isLt)] using (Fin.card_filter_val_lt (n:=t) (m:=i.val))
    exact (Finset.card_le_card hsub).trans_eq hc
  exact hh.trans (Nat.mul_le_mul_left D hcard)

theorem greedy_graph_candidates {V : Type*} [Fintype V] [DecidableEq V]
    (G J : SimpleGraph V) (family : Set (SimpleGraph V)) (t D : ℕ)
    (a : ℝ) (hJ : J ≤ G) (hJa : ∀ v, (J.degree v : ℝ) ≤ a)
    (havailable : ∀ K : SimpleGraph V, K ≤ G →
      (∀ v, (K.degree v : ℝ) ≤ a + D*t) →
      ∃ C : SimpleGraph V, C ∈ family ∧ C ≤ G ∧ (∀ v, C.degree v ≤ D) ∧ Disjoint C K) :
    ∃ C : Fin t → SimpleGraph V,
      (∀ i, C i ∈ family ∧ C i ≤ G ∧ (∀ v, (C i).degree v ≤ D) ∧ Disjoint (C i) J) ∧
      ∀ i j, i ≠ j → Disjoint (C i) (C j) := by
  let allowed := fun (_ : Fin t) (C : SimpleGraph V) =>
    C ∈ family ∧ C ≤ G ∧ (∀ v, C.degree v ≤ D) ∧ Disjoint C J
  obtain ⟨C, hC, hdisj⟩ := sequential_select_prefix t allowed Disjoint (⊥ : SimpleGraph V) (by
    intro i F hF
    have hFG (j : Fin t) : F j ≤ G := by
      by_cases hj : j.val < i.val
      · exact (hF.2.1 j hj).2.1
      · rw [hF.1 j (by omega)]; exact bot_le
    have hFD (j : Fin t) (v : V) : (F j).degree v ≤ D := by
      by_cases hj : j.val < i.val
      · exact (hF.2.1 j hj).2.2.1 v
      · rw [hF.1 j (by omega)]; simp
    let K := J ⊔ ⨆ j, F j
    have hKG : K ≤ G := sup_le hJ (iSup_le hFG)
    have hKD (v : V) : (K.degree v : ℝ) ≤ a + D*t := by
      have hsum := graph_degree_sup_le J (⨆ j, F j) v
      have hprior := graph_iSup_prefix_degree_bound F i D hFD hF.1 v
      have hprior' : ((⨆ j, F j).degree v : ℝ) ≤ D*(t:ℝ) := by
        exact_mod_cast hprior.trans (Nat.mul_le_mul_left D (Nat.le_of_lt i.isLt))
      have hsum' : (K.degree v : ℝ) ≤ (J.degree v : ℝ) + ((⨆ j, F j).degree v : ℝ) := by exact_mod_cast hsum
      linarith [hJa v]
    obtain ⟨A, hA, hAG, hAD, hAK⟩ := havailable K hKG (by intro v; convert hKD v using 1 <;> congr!)
    refine ⟨A, ⟨hA, hAG, hAD, hAK.mono_right le_sup_left⟩, ?_⟩
    intro j _
    exact (hAK.mono_right (le_trans (le_iSup F j) le_sup_right)).symm)
  refine ⟨C, hC, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hdisj i j h
  · exact (hdisj j i h).symm

end Oberwolfach
