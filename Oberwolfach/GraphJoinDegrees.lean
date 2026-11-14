module

public import Oberwolfach.SumGraphTools

@[expose] public section

/-! Degrees and adjacency in a join of two labelled finite graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def joinOnFin {a b : ℕ} (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) :
    SimpleGraph (Fin (a + b)) := (disjointSumOnFin Gᶜ Hᶜ)ᶜ

theorem disjointSumOnFin_degree_left {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (x : Fin a) :
    (disjointSumOnFin G H).degree (finSumFinEquiv (Sum.inl x)) = G.degree x := by
  have hh := SimpleGraph.degree_map_apply (G.sum H)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).toEmbedding (Sum.inl x)
  rw [sum_degree_inl] at hh
  simpa only [disjointSumOnFin, Equiv.toEmbedding_apply, ← SimpleGraph.ncard_neighborSet] using hh

theorem disjointSumOnFin_degree_right {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (x : Fin b) :
    (disjointSumOnFin G H).degree (finSumFinEquiv (Sum.inr x)) = H.degree x := by
  have hh := SimpleGraph.degree_map_apply (G.sum H)
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).toEmbedding (Sum.inr x)
  rw [sum_degree_inr] at hh
  simpa only [disjointSumOnFin, Equiv.toEmbedding_apply, ← SimpleGraph.ncard_neighborSet] using hh

theorem joinOnFin_adj {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (u v : Fin a ⊕ Fin b) :
    (joinOnFin G H).Adj (finSumFinEquiv u) (finSumFinEquiv v) ↔
      u ≠ v ∧ ¬ (Gᶜ.sum Hᶜ).Adj u v := by
  rw [joinOnFin, SimpleGraph.compl_adj, disjointSumOnFin_adj]
  exact and_congr_left (fun _ => not_congr finSumFinEquiv.injective.eq_iff)

theorem joinOnFin_adj_left {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (u v : Fin a) :
    (joinOnFin G H).Adj (finSumFinEquiv (Sum.inl u)) (finSumFinEquiv (Sum.inl v)) ↔
      G.Adj u v := by
  rw [joinOnFin_adj]
  simp only [SimpleGraph.sum_adj, SimpleGraph.compl_adj, ne_eq, Sum.inl.injEq]
  have hne := @SimpleGraph.Adj.ne _ G u v
  tauto

theorem joinOnFin_adj_right {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (u v : Fin b) :
    (joinOnFin G H).Adj (finSumFinEquiv (Sum.inr u)) (finSumFinEquiv (Sum.inr v)) ↔
      H.Adj u v := by
  rw [joinOnFin_adj]
  simp only [SimpleGraph.sum_adj, SimpleGraph.compl_adj, ne_eq, Sum.inr.injEq]
  have hne := @SimpleGraph.Adj.ne _ H u v
  tauto

theorem joinOnFin_adj_cross {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (u : Fin a) (v : Fin b) :
    (joinOnFin G H).Adj (finSumFinEquiv (Sum.inl u)) (finSumFinEquiv (Sum.inr v)) := by
  rw [joinOnFin_adj]
  simp [SimpleGraph.sum_adj]

theorem joinOnFin_degree_left {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (x : Fin a) :
    (joinOnFin G H).degree (finSumFinEquiv (Sum.inl x)) = b + G.degree x := by
  have hsum := disjointSumOnFin_degree_left Gᶜ Hᶜ x
  have hh := (disjointSumOnFin Gᶜ Hᶜ).degree_compl (v := finSumFinEquiv (Sum.inl x))
  have hcomp := G.degree_compl (v := x)
  simp only [← SimpleGraph.ncard_neighborSet] at hsum hcomp hh ⊢
  rw [hsum, hcomp] at hh
  simp only [Fintype.card_fin] at hh
  have hlt : (G.neighborSet x).ncard < a := by
    simpa only [← SimpleGraph.ncard_neighborSet, Fintype.card_fin] using G.degree_lt_card_verts x
  change ((disjointSumOnFin Gᶜ Hᶜ)ᶜ.neighborSet (finSumFinEquiv (Sum.inl x))).ncard = _
  rw [hh]
  omega

theorem joinOnFin_degree_right {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) (x : Fin b) :
    (joinOnFin G H).degree (finSumFinEquiv (Sum.inr x)) = a + H.degree x := by
  have hsum := disjointSumOnFin_degree_right Gᶜ Hᶜ x
  have hh := (disjointSumOnFin Gᶜ Hᶜ).degree_compl (v := finSumFinEquiv (Sum.inr x))
  have hcomp := H.degree_compl (v := x)
  simp only [← SimpleGraph.ncard_neighborSet] at hsum hcomp hh ⊢
  rw [hsum, hcomp] at hh
  simp only [Fintype.card_fin] at hh
  have hlt : (H.neighborSet x).ncard < b := by
    simpa only [← SimpleGraph.ncard_neighborSet, Fintype.card_fin] using H.degree_lt_card_verts x
  change ((disjointSumOnFin Gᶜ Hᶜ)ᶜ.neighborSet (finSumFinEquiv (Sum.inr x))).ncard = _
  rw [hh]
  omega

end Oberwolfach
