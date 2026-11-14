module

public import Oberwolfach.RootComparisonHosts

@[expose] public section

/-! Realize a relation on two disjoint subsets as a simple graph. Its
maximum degree is bounded by the separate row and column bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def bipartiteRelationGraph (A B : Finset V) (hAB : Disjoint A B) (E : V→V→Prop) : SimpleGraph V where
  Adj a b := (a∈A ∧ b∈B ∧ E a b) ∨ (b∈A ∧ a∈B ∧ E b a)
  symm := ⟨by intro a b h;exact h.symm⟩
  loopless := ⟨by intro a h;rcases h with h|h <;> exact Finset.disjoint_left.mp hAB h.1 h.2.1⟩

theorem bipartiteRelationGraph_left (A B : Finset V) (hAB : Disjoint A B) (E : V→V→Prop)
    {a b : V} (ha : a∈A) :
    (bipartiteRelationGraph A B hAB E).Adj a b ↔ b∈B ∧ E a b := by
  have haB : a∉B := fun h=>Finset.disjoint_left.mp hAB ha h
  simp [bipartiteRelationGraph,ha,haB]

theorem bipartiteRelationGraph_right (A B : Finset V) (hAB : Disjoint A B) (E : V→V→Prop)
    {a b : V} (ha : a∈B) :
    (bipartiteRelationGraph A B hAB E).Adj a b ↔ b∈A ∧ E b a := by
  have haA : a∉A := fun h=>Finset.disjoint_left.mp hAB h ha
  simp [bipartiteRelationGraph,ha,haA]

theorem bipartiteRelationGraph_outside (A B : Finset V) (hAB : Disjoint A B) (E : V→V→Prop)
    {a b : V} (ha : a∉A) (hb : a∉B) :
    ¬(bipartiteRelationGraph A B hAB E).Adj a b := by
  simp [bipartiteRelationGraph,ha,hb]

theorem bipartiteRelationGraph_degree_bound (A B : Finset V) (hAB : Disjoint A B)
    (E : V→V→Prop) (L : ℝ) (hL : 0≤L)
    (hrow : ∀ a∈A,((Finset.univ.filter (E a)).card:ℝ)≤L)
    (hcol : ∀ b∈B,((Finset.univ.filter (fun a=>E a b)).card:ℝ)≤L) (v : V) :
    ((bipartiteRelationGraph A B hAB E).degree v:ℝ)≤L := by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hvA : v∈A
  · apply le_trans _ (hrow v hvA)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((bipartiteRelationGraph_left A B hAB E hvA).mp
        ((SimpleGraph.mem_neighborFinset _ v w).mp hw)).2⟩
  by_cases hvB : v∈B
  · apply le_trans _ (hcol v hvB)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((bipartiteRelationGraph_right A B hAB E hvB).mp
        ((SimpleGraph.mem_neighborFinset _ v w).mp hw)).2⟩
  · have he : (bipartiteRelationGraph A B hAB E).neighborFinset v=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact bipartiteRelationGraph_outside A B hAB E hvA hvB
        ((SimpleGraph.mem_neighborFinset _ v w).mp hw)
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact hL

end Oberwolfach
