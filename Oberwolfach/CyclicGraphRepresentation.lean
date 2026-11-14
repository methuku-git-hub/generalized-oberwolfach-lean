module

public import Oberwolfach.CyclicFractionalDecomposition
public import Oberwolfach.FractionalRelabeling

@[expose] public section

/-! Recover the interface representation from a graph with a specified
cyclic partition. The labelling equivalence covers every host vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def leftCyclicInterface {k : ℕ} {X Y : Type*}
    (G : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)))
    (i : Fin (k + 2)) (x : X) (y : Y) : Prop :=
  G.Adj (Sum.inl (i, x)) (Sum.inr (i, y))

def rightCyclicInterface {k : ℕ} {X Y : Type*}
    (G : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)))
    (i : Fin (k + 2)) (y : Y) (x : X) : Prop :=
  G.Adj (Sum.inr (i, y)) (Sum.inl (finRotate (k + 2) i, x))

theorem cyclicGraph_interface_reconstruction {k : ℕ} {X Y : Type*}
    (G : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)))
    (hcyc : G ≤ cyclicInterfaceGraph (fun _ _ _ => True) (fun _ _ _ => True)) :
    G = cyclicInterfaceGraph (leftCyclicInterface G) (rightCyclicInterface G) := by
  ext a b
  have hcross (i j : Fin (k + 2)) (x : X) (y : Y) :
      G.Adj (Sum.inl (i, x)) (Sum.inr (j, y)) ↔
      (i = j ∧ leftCyclicInterface G i x y) ∨
        (i = finRotate (k + 2) j ∧ rightCyclicInterface G j y x) := by
    constructor
    · intro h
      have hc := hcyc h
      change (i = j ∧ True) ∨ (i = finRotate (k + 2) j ∧ True) at hc
      rcases hc with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h.symm⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact h
      · exact h.symm
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change G.Adj (Sum.inl a) (Sum.inl b) ↔ False
      exact ⟨fun h => hcyc h, False.elim⟩
    | inr b => exact hcross a.1 b.1 a.2 b.2
  | inr a =>
    cases b with
    | inr b =>
      change G.Adj (Sum.inr a) (Sum.inr b) ↔ False
      exact ⟨fun h => hcyc h, False.elim⟩
    | inl b =>
      change G.Adj (Sum.inr a) (Sum.inl b) ↔ _
      rw [G.adj_comm]
      exact hcross b.1 a.1 b.2 a.2

theorem cyclic_graph_has_fractional_cycles {k : ℕ} {X Y V : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [Nonempty X]
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (e : ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)) ≃ V)
    (hcyc : G.comap e ≤
      cyclicInterfaceGraph (fun _ _ _ => True) (fun _ _ _ => True))
    (δ : ℝ) (hn : 0 < Fintype.card Y)
    (hthreshold : (k + 2 : ℝ) * Fintype.card Y ≤ (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (leftCyclicInterface (G.comap e) i x)).card)
    (hY : ∀ i y,
      (Finset.univ.filter (fun x => leftCyclicInterface (G.comap e) i x y)).card =
      (Finset.univ.filter (rightCyclicInterface (G.comap e) i y)).card)
    (hX : ∀ i z,
      (Finset.univ.filter (fun y => rightCyclicInterface (G.comap e) i y z)).card =
      (Finset.univ.filter (leftCyclicInterface (G.comap e) (finRotate (k + 2) i) z)).card) :
    HasFractionalDecomposition G (fun H => IsEmbeddedCycle H ((k + 2) * 2) ∧
      ∃ p : Fin (k + 2) → X × Y × X, H = (alternatingTupleGraph p).map e.toEmbedding) := by
  have hh := cyclicInterfaceGraph_has_fractional_cycles
    (leftCyclicInterface (G.comap e)) (rightCyclicInterface (G.comap e))
    δ hn hthreshold hdL hY hX
  rw [← cyclicGraph_interface_reconstruction (G.comap e) hcyc] at hh
  have hm := hh.map e
  have hG : (G.comap e).map e.toEmbedding = G := by
    ext u v
    simp only [← SimpleGraph.comap_symm _ e, SimpleGraph.comap_adj,
      Equiv.toEmbedding_apply, Equiv.apply_symm_apply]
  rw [hG] at hm
  apply hm.mono_property
  rintro H ⟨K, ⟨hK, p, rfl⟩, rfl⟩
  exact ⟨hK.map e.toEmbedding, p, rfl⟩

end Oberwolfach
