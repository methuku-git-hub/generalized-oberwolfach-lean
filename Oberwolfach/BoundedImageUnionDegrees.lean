module

public import Oberwolfach.Definitions

@[expose] public section
/-! Bound the degree of a union of embedded degree-two graphs by the number
of source vertices mapped to each physical vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem degree_two_image_union_bound (H:I→SimpleGraph V) (occ:I→V→Prop)
    (hdeg:∀ i v,(H i).degree v≤(if occ i v then 2 else 0)) (v:V):
    ((Finset.univ.biUnion (fun i=>(H i).neighborFinset v)).card:ℕ)≤
      2*(Finset.univ.filter (fun i=>occ i v)).card := by
  calc
    _ ≤ ∑ i,(H i).degree v:=by
      have hh:=Finset.card_biUnion_le (s:=Finset.univ) (t:=fun i=>(H i).neighborFinset v)
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh
    _ ≤ ∑ i,(if occ i v then 2 else 0):=Finset.sum_le_sum (fun i _=>hdeg i v)
    _ = 2*(Finset.univ.filter (fun i=>occ i v)).card:=by simp [Finset.sum_ite, Nat.mul_comm]

theorem bounded_degree_two_union_from_occurrences (H:I→SimpleGraph V) (occ:I→V→Prop)
    (hdeg:∀ i v,(H i).degree v≤(if occ i v then 2 else 0))
    (G:SimpleGraph V) (hcover:∀ v,(G.neighborFinset v)⊆Finset.univ.biUnion (fun i=>(H i).neighborFinset v))
    (M:ℕ) (hocc:∀ v,(Finset.univ.filter (fun i=>occ i v)).card≤M):
    ∀ v,G.degree v≤2*M := by
  intro v
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  exact (Finset.card_le_card (hcover v)).trans ((degree_two_image_union_bound H occ hdeg v).trans (Nat.mul_le_mul_left 2 (hocc v)))
end Oberwolfach
