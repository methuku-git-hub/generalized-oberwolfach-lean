module

public import Oberwolfach.OrdinaryCycleIncidence

@[expose] public section

/-! Restricting an ambient graph-weight function to actual cycles in the
host preserves each edge-load equation without adding representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sum_restrict_of_zero {I : Type*} [Fintype I]
    (P : I → Prop) (f : I → ℝ) (hf : ∀ i,¬P i → f i=0) :
    (∑ i,f i)=∑ i : {i // P i},f i.val := by
  have hh := Fintype.sum_subtype_add_sum_subtype P f
  have hz : (∑ i : {i // ¬P i},f i.val)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hf i.val i.property
  rw [hz,add_zero] at hh
  exact hh.symm

theorem ordinaryCycle_load_from_graph_weights {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (a : SimpleGraph V → ℝ)
    (ha : ∀ C,0≤a C) (hs : ∀ C,0<a C → C≤G ∧ IsEmbeddedCycle C r)
    (e : G.edgeSet) :
    (∑ C : OrdinaryCycle G r,a C.val.val*ordinaryCycleIncidence G r C e)=
      ∑ C : SimpleGraph V,if e.val∈C.edgeSet then a C else 0 := by
  have hzero (C : SimpleGraph V) (hC : ¬(C≤G ∧ IsEmbeddedCycle C r)) : a C=0 := by
    by_contra hn
    exact hC (hs C (lt_of_le_of_ne (ha C) (Ne.symm hn)))
  symm
  calc
    _ = ∑ C : EmbeddedCycleFamily V r,if e.val∈C.val.edgeSet then a C.val else 0 := by
      apply finite_sum_restrict_of_zero (fun C => IsEmbeddedCycle C r)
      intro C hC
      have hz := hzero C (fun h => hC h.2)
      simp only [hz,ite_self]
    _ = ∑ C : OrdinaryCycle G r,if e.val∈C.val.val.edgeSet then a C.val.val else 0 := by
      apply finite_sum_restrict_of_zero (fun C : EmbeddedCycleFamily V r => C.val≤G)
      intro C hC
      have hz := hzero C.val (fun h => hC h.1)
      simp only [hz,ite_self]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      dsimp [ordinaryCycleIncidence]
      split_ifs <;> simp

end Oberwolfach
