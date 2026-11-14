module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Exact transport of neighbour counts by a fixed permutation. The root
is an arbitrary ambient vertex, not necessarily a member of the set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem permutation_neighbour_filter_image
    {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph V) (π : Equiv.Perm V)
    (T : Finset V) (x : V) :
    (T.filter (fun v=>P.Adj x (π v))).image π=P.neighborFinset x∩T.image π := by
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨v,⟨hv,hadj⟩,heq⟩
    exact ⟨heq ▸ hadj,⟨v,hv,heq⟩⟩
  · rintro ⟨hadj,v,hv,heq⟩
    exact ⟨v,⟨hv,heq.symm ▸ hadj⟩,heq⟩

theorem permutation_neighbour_filter_card
    {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph V) (π : Equiv.Perm V)
    (T : Finset V) (x : V) :
    (T.filter (fun v=>P.Adj x (π v))).card=(P.neighborFinset x∩T.image π).card := by
  rw [← permutation_neighbour_filter_image,Finset.card_image_of_injective _ π.injective]

theorem permutation_neighbour_domain_card
    {V : Type*} [Fintype V] [DecidableEq V] (P : SimpleGraph V) (π : Equiv.Perm V) (x : V) :
    (Finset.univ.filter (fun v=>P.Adj x (π v))).card=P.degree x := by
  rw [permutation_neighbour_filter_card]
  have him : Finset.univ.image π=(Finset.univ : Finset V) := by
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and,iff_true]
    exact π.surjective z
  rw [him,Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree]

end Oberwolfach
