module

public import Oberwolfach.ProfileVertexRestriction

@[expose] public section

/-! The class profile after omitting one specified vertex. Deletions
exclude the other fixed vertices while preserving the original root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_erase_class_card (F : Finset (Σ i,V i)) (v : Σ i,V i) (hv : v∈F) (i : I) :
    (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F.erase v)).card=
      (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F)).card-
        (if v.1=i then 1 else 0) := by
  rcases v with ⟨j,v⟩
  by_cases hi : i=j
  · subst j
    have he : Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F.erase ⟨i,v⟩)=
        (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F)).erase v := by
      ext u
      simp [Finset.mem_erase,Sigma.mk.inj_iff]
    have hv' : v∈Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    rw [he,Finset.card_erase_of_mem hv']
    simp
  · have he : Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F.erase ⟨j,v⟩)=
        Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F) := by
      ext u
      have hne : (⟨i,u⟩ : Σ i,V i)≠⟨j,v⟩ := fun h => hi (congrArg Sigma.fst h)
      simp only [Finset.mem_filter,Finset.mem_univ,Finset.mem_erase,true_and]
      exact ⟨fun h => h.2,fun h => ⟨hne,h⟩⟩
    rw [he]
    simp [Ne.symm hi]

theorem root_omitted_support_avoids (F Z : Finset (Σ i,V i)) (v : Σ i,V i)
    (hd : Disjoint F (Z.erase v)) :
    ∀ x∈F.erase v,x∉Z := by
  intro x hx hz
  have hx' := Finset.mem_erase.mp hx
  exact Finset.disjoint_left.mp hd hx'.2 (Finset.mem_erase.mpr ⟨hx'.1,hz⟩)

theorem root_omitted_preimage_class_card (F Z : Finset (Σ i,V i)) (v : Σ i,V i)
    (hv : v∈F) (hd : Disjoint F (Z.erase v)) (i : I) :
    (Finset.univ.filter (fun u : ProfileRemainingClass Z i =>
      profileComplementEmbedding Z ⟨i,u⟩∈F.erase v)).card=
      (Finset.univ.filter (fun u : V i => (⟨i,u⟩ : Σ i,V i)∈F)).card-
        (if v.1=i then 1 else 0) := by
  let R : Unit → Finset (Σ i,V i) := fun _ => F.erase v
  let D : RestrictedResource R (profileComplementEmbedding Z) := ⟨(),by
    intro x hx
    exact (profileComplementEmbedding_range Z x).mpr (root_omitted_support_avoids F Z v hd x hx)⟩
  have hh := profile_restricted_resource_class_card R Z D i
  have he : Finset.univ.filter (fun u : ProfileRemainingClass Z i =>
      (⟨i,u⟩ : Σ j,ProfileRemainingClass Z j)∈restrictedResourceSet R (profileComplementEmbedding Z) D)=
      Finset.univ.filter (fun u : ProfileRemainingClass Z i =>
        profileComplementEmbedding Z ⟨i,u⟩∈F.erase v) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,restrictedResourceSet_mem,R,D]
  rw [he] at hh
  exact hh.trans (profile_erase_class_card F v hv i)

end Oberwolfach
