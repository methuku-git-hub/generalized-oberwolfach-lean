module

public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! Disjoint restricted resources remain disjoint in the original fixed
resource domain; the candidate sets are not enlarged or resampled. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C]

theorem restricted_resource_disjoint_in_original_domain
    (R:C→Finset V) (e:W↪V) (a b:RestrictedResource R e)
    (h:Disjoint (restrictedResourceSet R e a) (restrictedResourceSet R e b)):
    Disjoint (R a.val) (R b.val):=by
  rw [←restrictedResourceSet_image R e a,←restrictedResourceSet_image R e b]
  exact (Finset.disjoint_image e.injective).2 h
end Oberwolfach
