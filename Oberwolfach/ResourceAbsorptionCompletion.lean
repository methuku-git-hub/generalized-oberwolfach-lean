module

public import Oberwolfach.ResourceRestriction

@[expose] public section

/-! Complete a matching on the surviving vertices with an exact
absorption of its leftover; all unions are equalities of vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C]

theorem resource_restriction_absorption_completion (R : C → Finset V) (e : W ↪ V)
    (Z : Finset V) (he : ∀ v,(∃ w,e w=v) ↔ v∉Z)
    (M : Finset (RestrictedResource R e))
    (hM : ∀ D∈M,∀ E∈M,D≠E → Disjoint (restrictedResourceSet R e D) (restrictedResourceSet R e E))
    (habs : HasResourceDecomposition R (Z∪(Finset.univ\M.biUnion (restrictedResourceSet R e)).image e)) :
    HasResourceDecomposition R Finset.univ := by
  let A := M.biUnion (restrictedResourceSet R e)
  have hA : HasResourceDecomposition R (A.image e) :=
    restricted_resource_decomposition_lift R e A ⟨M,hM,rfl⟩
  have hdisj : Disjoint (A.image e) (Z∪(Finset.univ\A).image e) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hw with hz | hw
    · exact (he _).mp ⟨x,rfl⟩ hz
    · obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hw
      have hxy' := e.injective hxy
      subst y
      exact (Finset.mem_sdiff.mp hy).2 hx
  have hU : A.image e∪(Z∪(Finset.univ\A).image e)=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    by_cases hz : v∈Z
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hz)
    · obtain ⟨x,rfl⟩ := (he v).mpr hz
      by_cases hx : x∈A
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨x,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩))
  rw [← hU]
  exact resource_decomposition_union R _ _ hA habs hdisj

end Oberwolfach
