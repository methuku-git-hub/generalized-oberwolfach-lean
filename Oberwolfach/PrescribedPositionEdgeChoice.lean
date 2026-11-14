module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Oberwolfach.FiniteHighEventsCommon
public import Mathlib.Data.Sym.Sym2

@[expose] public section
/-! In a graph of maximum degree two, a vertex set meeting every edge has
size at least half the number of edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_position_edge_choice (Q:SimpleGraph X) (S:Finset X)
    (hdeg:∀ x,Q.degree x≤2) (hE:2*S.card<Q.edgeFinset.card):
    ∃ x y,Q.Adj x y ∧ x∉S ∧ y∉S := by
  by_contra hn
  have hcover:Q.edgeFinset⊆S.biUnion (fun v=>Q.incidenceFinset v):=by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:Q.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
      have hs:x∈S ∨ y∈S:=by
        by_contra h
        push_neg at h
        exact hn ⟨x,y,hxy,h.1,h.2⟩
      rcases hs with hx|hy
      · apply Finset.mem_biUnion.mpr
        refine ⟨x,hx,?_⟩
        rw [Q.incidenceFinset_eq_filter x]
        simp [he]
      · apply Finset.mem_biUnion.mpr
        refine ⟨y,hy,?_⟩
        rw [Q.incidenceFinset_eq_filter y]
        simp [he]
  have hc:Q.edgeFinset.card≤2*S.card:=by
    calc
      Q.edgeFinset.card≤(S.biUnion (fun v=>Q.incidenceFinset v)).card:=Finset.card_le_card hcover
      _≤∑ x∈S,(Q.incidenceFinset x).card:=Finset.card_biUnion_le
      _≤∑ _x∈S,2:=by
        apply Finset.sum_le_sum
        intro x hx
        rw [Q.card_incidenceFinset_eq_degree]
        exact hdeg x
      _=2*S.card:=by simp [Nat.mul_comm]
  omega
end Oberwolfach
