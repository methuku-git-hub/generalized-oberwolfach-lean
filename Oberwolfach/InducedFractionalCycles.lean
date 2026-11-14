module

public import Oberwolfach.FractionalSubgraphs

@[expose] public section

/-! Fractional decompositions on an induced vertex set lifted back to
actual subgraphs on the ambient vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def spanningRestriction {V : Type*} (G : SimpleGraph V) (S : Finset V) : SimpleGraph V :=
  (G.induce (S:Set V)).map (Function.Embedding.subtype _)

theorem spanningRestriction_adj {V : Type*} (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (spanningRestriction G S).Adj u v ↔ G.Adj u v ∧ u∈S ∧ v∈S := by
  rw [spanningRestriction,SimpleGraph.map_adj]
  constructor
  · rintro ⟨x,y,hxy,hx,hy⟩
    subst u
    subst v
    exact ⟨hxy,x.property,y.property⟩
  · rintro ⟨hG,hu,hv⟩
    exact ⟨⟨u,hu⟩,⟨v,hv⟩,hG,rfl,rfl⟩

theorem spanningRestriction_le {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    spanningRestriction G S≤G := fun u v h => ((spanningRestriction_adj G S u v).mp h).1

theorem spanningRestriction_support {V : Type*} (G : SimpleGraph V) (S : Finset V) :
    (spanningRestriction G S).support⊆(S:Set V) := by
  intro u hu
  obtain ⟨v,huv⟩ := hu
  exact ((spanningRestriction_adj G S u v).mp huv).2.1

theorem induced_degree_intersection {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (v : (S:Set V)) :
    (G.induce (S:Set V)).degree v=(G.neighborFinset v.val∩S).card := by
  have hh := congrArg Finset.card (G.map_neighborFinset_induce (s:=(S:Set V)) v)
  simp only [Finset.card_map,SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.ncard_neighborSet] at hh ⊢
  simpa using hh

theorem cycle_fractional_on_subset (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],∀ (G : SimpleGraph V) (S : Finset V),
      N≤S.card → (∀ v∈S,(cycleThreshold r+α)*S.card≤((G.neighborFinset v∩S).card:ℝ)) →
      HasFractionalDecomposition (spanningRestriction G S) (fun C => IsEmbeddedCycle C r) := by
  obtain ⟨N,hN⟩ := cycle_fractional_positive_margin_finite r hr α hα
  refine ⟨N,?_⟩
  intro V _ _ G S hn hdeg
  have hh : HasFractionalDecomposition (G.induce (S:Set V)) (fun C => IsEmbeddedCycle C r) := by
    apply hN (S:Set V) (by simpa using hn)
    intro v
    have hd := hdeg v.val v.property
    have he := induced_degree_intersection G S v
    simp only [← SimpleGraph.ncard_neighborSet] at he ⊢
    rw [he]
    simpa only [Fintype.card_coe,Finset.coe_sort_coe] using hd
  exact hh.map_embedded_cycles (Function.Embedding.subtype _)

end Oberwolfach
