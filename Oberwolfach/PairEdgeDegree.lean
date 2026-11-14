module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Card

@[expose] public section

/-! A finite family of directed pairs with injective tails and heads has
at most two distinct incident unordered edges at every vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [DecidableEq V]

theorem pair_edge_incident_card_le_two (tail head : I → V)
    (ht : Function.Injective tail) (hh : Function.Injective head) (v : V) :
    ((Finset.univ.image (fun i => ({tail i,head i} : Finset V))).filter (fun e => v∈e)).card≤2 := by
  rw [Finset.filter_image]
  apply Finset.card_image_le.trans
  have he : Finset.univ.filter (fun i => v∈({tail i,head i}:Finset V))=
      (Finset.univ.filter (fun i => tail i=v))∪(Finset.univ.filter (fun i => head i=v)) := by
    ext i;simp [eq_comm]
  rw [he]
  apply (Finset.card_union_le _ _).trans
  have h₁ : (Finset.univ.filter (fun i => tail i=v)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact ht ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have h₂ : (Finset.univ.filter (fun i => head i=v)).card≤1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact hh ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  omega

end Oberwolfach
