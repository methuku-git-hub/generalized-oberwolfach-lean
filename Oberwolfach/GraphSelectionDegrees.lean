module

public import Oberwolfach.GraphSelectionTests
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Local and global degrees of the union of selected graphs. The local
bound counts prior choices that actually meet the next support; it is
not replaced by the generally larger degree of the full union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] {N : ℕ}

theorem graph_iSup_local_degree_bound (F : J→SimpleGraph V) (T : Finset V) (v : V) (D : ℕ)
    (hD : ∀ j,(F j).degree v ≤ D) :
    (((⨆ j,F j).neighborFinset v)∩T).card ≤
      D*(Finset.univ.filter (fun j=>∃ w∈T,(F j).Adj v w)).card := by
  let A := Finset.univ.filter (fun j=>∃ w∈T,(F j).Adj v w)
  have he : ((⨆ j,F j).neighborFinset v)∩T=A.biUnion (fun j=>(F j).neighborFinset v∩T) := by
    ext w
    simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,SimpleGraph.iSup_adj,Finset.mem_biUnion,A,
      Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨j,hj⟩,hw⟩;exact ⟨j,⟨w,hw,hj⟩,hj,hw⟩
    · rintro ⟨j,hj,hjw,hw⟩;exact ⟨⟨j,hjw⟩,hw⟩
  rw [he]
  calc
    _ ≤ ∑ j∈A,((F j).neighborFinset v∩T).card := Finset.card_biUnion_le
    _ ≤ ∑ _j∈A,D := Finset.sum_le_sum (fun j _=>
      ((Finset.card_le_card (Finset.inter_subset_left)).trans (by simpa using hD j)))
    _ = _ := by simp [A,Nat.mul_comm]

theorem graph_iSup_global_degree_bound (F : J→SimpleGraph V) (S : J→Finset V) (D : ℕ)
    (hsup : ∀ j,GraphSupportedOn (S j) (F j)) (hD : ∀ j v,(F j).degree v ≤ D) (v : V) :
    (⨆ j,F j).degree v ≤ D*(Finset.univ.filter (fun j=>v∈S j)).card := by
  have hh := graph_iSup_local_degree_bound F Finset.univ v D (fun j=>hD j v)
  simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
  apply hh.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro j hj
  obtain ⟨w,hw,hvw⟩ := (Finset.mem_filter.mp hj).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hsup j v w hvw).1⟩

theorem graphSelection_counter_eq (S : Fin N→Finset V) (F : Fin N→SimpleGraph V)
    (x : SelectionVertexTest S)
    (hfuture : ∀ j,x.val.1.val ≤ j.val → F j=⊥)
    (hsup : ∀ j,GraphSupportedOn (S j) (F j)) :
    (Finset.univ.filter (fun j=>∃ w∈S x.val.1,(F j).Adj x.val.2 w)).card=
      selectionCounter (graphSelectionActive S) (graphSelectionHit S) F x := by
  apply congrArg Finset.card
  ext j
  simp only [selectionCounter,Finset.mem_filter,Finset.mem_univ,true_and,graphSelectionActive,graphSelectionHit]
  constructor
  · rintro ⟨w,hw,hvw⟩
    have hji : j.val < x.val.1.val := by
      by_contra hn
      have hj := hfuture j (by omega)
      rw [hj] at hvw
      exact hvw.elim
    exact ⟨⟨hji,(hsup j x.val.2 w hvw).1⟩,w,hw,hvw⟩
  · rintro ⟨ha,hh⟩;exact hh

theorem spanningRestriction_degree (F : SimpleGraph V) (S : Finset V) (v : V) :
    (spanningRestriction F S).degree v=
      if v∈S then (F.neighborFinset v∩S).card else 0 := by
  have he : (spanningRestriction F S).neighborFinset v=
      if v∈S then F.neighborFinset v∩S else ∅ := by
    ext w
    by_cases hv : v∈S <;> simp [SimpleGraph.mem_neighborFinset,spanningRestriction_adj,hv]
  rw [← SimpleGraph.card_neighborFinset_eq_degree,he]
  split_ifs <;> simp

theorem disjoint_of_restricted_union (F : J→SimpleGraph V) (S : Finset V) (C : SimpleGraph V)
    (hC : GraphSupportedOn S C) (hdisj : Disjoint C (spanningRestriction (⨆ j,F j) S)) :
    ∀ j,Disjoint (F j) C := by
  intro j
  apply disjoint_iff_inf_le.mpr
  intro v w h
  have hs := hC v w h.2
  have hJ : (spanningRestriction (⨆ j,F j) S).Adj v w :=
    (spanningRestriction_adj _ _ _ _).mpr ⟨SimpleGraph.iSup_adj.mpr ⟨j,h.1⟩,hs⟩
  exact (disjoint_graphs_no_common_edge C _ hdisj v w h.2 hJ).elim

end Oberwolfach
