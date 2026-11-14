module

public import Oberwolfach.ProfileVertexRestriction

@[expose] public section

/-! Exact class counts under the embedding of the complement of a
fixed vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_avoiding_preimage_class_card (F Z : Finset (Σ i,V i))
    (hd : Disjoint F Z) (i : I) :
    (Finset.univ.filter (fun u : ProfileRemainingClass Z i =>
      profileComplementEmbedding Z ⟨i,u⟩∈F)).card=
      (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F)).card := by
  let R : Unit → Finset (Σ i,V i) := fun _ => F
  let D : RestrictedResource R (profileComplementEmbedding Z) := ⟨(),by
    intro x hx
    exact (profileComplementEmbedding_range Z x).mpr (fun hz => Finset.disjoint_left.mp hd hx hz)⟩
  have hh := profile_restricted_resource_class_card R Z D i
  have he : Finset.univ.filter (fun u : ProfileRemainingClass Z i =>
      (⟨i,u⟩ : Σ j,ProfileRemainingClass Z j)∈restrictedResourceSet R (profileComplementEmbedding Z) D)=
      Finset.univ.filter (fun u : ProfileRemainingClass Z i => profileComplementEmbedding Z ⟨i,u⟩∈F) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,restrictedResourceSet_mem,R,D]
  rw [he] at hh
  exact hh

end Oberwolfach
