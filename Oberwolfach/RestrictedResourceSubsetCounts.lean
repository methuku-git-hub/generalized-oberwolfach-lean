module

public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! Restriction to a sampled resource set does not change the number of
resources of a surviving candidate in a fixed hub class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C:Type} [Fintype V] [Fintype W] [Fintype C] [DecidableEq V] [DecidableEq W] [DecidableEq C]

def restrictedResourceSubset (e:W↪V) (S:Finset V):Finset W:=
  Finset.univ.filter (fun w=>e w∈S)

theorem restricted_resource_subset_card
    (R:C→Finset V) (e:W↪V) (S:Finset V) (c:RestrictedResource R e):
    ((restrictedResourceSet R e c)∩restrictedResourceSubset e S).card=(R c.val∩S).card := by
  have himage : ((restrictedResourceSet R e c)∩restrictedResourceSubset e S).image e=R c.val∩S := by
    ext v
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp h
      exact Finset.mem_inter.mpr ⟨(restrictedResourceSet_mem R e c a).mp (Finset.mem_inter.mp ha).1,
        (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2⟩
    · intro h
      obtain ⟨hr,hs⟩:=Finset.mem_inter.mp h
      obtain ⟨a,rfl⟩:=c.property v hr
      refine Finset.mem_image.mpr ⟨a,Finset.mem_inter.mpr ⟨?_,?_⟩,rfl⟩
      · exact (restrictedResourceSet_mem R e c a).mpr hr
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩
  rw [←himage,Finset.card_image_of_injective _ e.injective]
end Oberwolfach
