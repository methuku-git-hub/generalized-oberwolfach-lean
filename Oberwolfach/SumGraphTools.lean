module

public import Oberwolfach.CycleComponents
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! Relabelling a disjoint graph sum on a single finite vertex type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sum_degree_inl {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) :
    (G.sum H).degree (Sum.inl v) = G.degree v := by
  have hs : (G.sum H).neighborSet (Sum.inl v) = Sum.inl '' G.neighborSet v := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, SimpleGraph.sum_adj]
  rw [← SimpleGraph.ncard_neighborSet, hs,
    Set.ncard_image_of_injective _ Sum.inl_injective, SimpleGraph.ncard_neighborSet]

theorem sum_degree_inr {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (v : W) :
    (G.sum H).degree (Sum.inr v) = H.degree v := by
  have hs : (G.sum H).neighborSet (Sum.inr v) = Sum.inr '' H.neighborSet v := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborSet, SimpleGraph.sum_adj]
  rw [← SimpleGraph.ncard_neighborSet, hs,
    Set.ncard_image_of_injective _ Sum.inr_injective, SimpleGraph.ncard_neighborSet]

def disjointSumOnFin {a b : ℕ} (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) :
    SimpleGraph (Fin (a + b)) :=
  (G.sum H).map (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).toEmbedding

def sumLeftEmbedding (a b : ℕ) : Fin a ↪ Fin (a + b) :=
  Function.Embedding.inl.trans
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).toEmbedding

def sumLeftVertices (a b : ℕ) : Finset (Fin (a + b)) :=
  Finset.univ.map (sumLeftEmbedding a b)

theorem mem_sumLeftVertices_inl {a b : ℕ} (v : Fin a) :
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) (Sum.inl v) ∈ sumLeftVertices a b := by
  exact Finset.mem_map.mpr ⟨v, Finset.mem_univ v, rfl⟩

theorem not_mem_sumLeftVertices_inr {a b : ℕ} (v : Fin b) :
    (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) (Sum.inr v) ∉ sumLeftVertices a b := by
  intro hv
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_map.mp hv
  change finSumFinEquiv (Sum.inl x) = finSumFinEquiv (Sum.inr v) at hxeq
  cases (finSumFinEquiv.injective hxeq)

theorem disjointSumOnFin_adj {a b : ℕ} (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b))
    (u v : Fin a ⊕ Fin b) :
    (disjointSumOnFin G H).Adj (finSumFinEquiv u) (finSumFinEquiv v) ↔
      (G.sum H).Adj u v := by
  exact SimpleGraph.map_adj_apply

theorem disjointSumOnFin_closed {a b : ℕ} (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b))
    (u v : Fin (a + b)) (huv : (disjointSumOnFin G H).Adj u v) :
    u ∈ sumLeftVertices a b ↔ v ∈ sumLeftVertices a b := by
  obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective u
  obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective v
  rw [disjointSumOnFin_adj] at huv
  cases u with
  | inl x =>
    cases v with
    | inl y => exact iff_of_true (mem_sumLeftVertices_inl x) (mem_sumLeftVertices_inl y)
    | inr y => cases huv
  | inr x =>
    cases v with
    | inl y => cases huv
    | inr y => exact iff_of_false (not_mem_sumLeftVertices_inr x) (not_mem_sumLeftVertices_inr y)

theorem disjointSumOnFin_regular {a b d : ℕ} (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b))
    (hG : G.IsRegularOfDegree d) (hH : H.IsRegularOfDegree d) :
    (disjointSumOnFin G H).IsRegularOfDegree d := by
  intro x
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  obtain ⟨y, rfl⟩ := e.surjective x
  have hh := SimpleGraph.degree_map_apply (G.sum H) e.toEmbedding y
  have hdeg : (G.sum H).degree y = d := by
    cases y with
    | inl v => exact (sum_degree_inl G H v).trans (hG v)
    | inr v => exact (sum_degree_inr G H v).trans (hH v)
  rw [hdeg] at hh
  simpa only [disjointSumOnFin, e, SimpleGraph.Iso.map_apply,
    Equiv.toEmbedding_apply, ← SimpleGraph.ncard_neighborSet] using hh

theorem disjointSumOnFin_internal_left {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) :
    internalEdges (disjointSumOnFin G H) (sumLeftVertices a b) =
      (G.map (sumLeftEmbedding a b)).edgeFinset := by
  classical
  have hemb (x : Fin a) (u : Fin a ⊕ Fin b) :
      sumLeftEmbedding a b x = finSumFinEquiv u ↔ Sum.inl x = u := by
    change finSumFinEquiv (Sum.inl x) = finSumFinEquiv u ↔ _
    exact finSumFinEquiv.injective.eq_iff
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective u
    obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).surjective v
    rw [mem_internalEdges, disjointSumOnFin_adj, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet,
      SimpleGraph.map_adj]
    cases u <;> cases v <;>
      simp only [SimpleGraph.sum_adj, mem_sumLeftVertices_inl, not_mem_sumLeftVertices_inr,
        hemb, Sum.inl.injEq, Sum.inl_ne_inr] <;> aesop

theorem disjointSumOnFin_internal_left_card {a b : ℕ}
    (G : SimpleGraph (Fin a)) (H : SimpleGraph (Fin b)) :
    (internalEdges (disjointSumOnFin G H) (sumLeftVertices a b)).card = G.edgeFinset.card := by
  rw [disjointSumOnFin_internal_left]
  simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    using SimpleGraph.card_edgeFinset_map (sumLeftEmbedding a b) G

end Oberwolfach
