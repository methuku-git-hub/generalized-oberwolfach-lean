module

public import Oberwolfach.OrdinaryCleanupProfileFromDeepSample
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! The actual physical symmetric edit and the original raw tests supply
    the typed cleanup profile on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_cleanup_profile_from_physical_edit
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density) (hs:∀u,s u j=pH)
    (hdis:Disjoint Q F) (hmin:∀v,density*X.card≤((X∩P.neighborFinset v).card:ℝ))
    (hrows:RawOrdinaryRows P π d 3 X pR s j tR raw)
    (hcolumns:RawOrdinaryDomainIndices F π d 3 Z pH j tH raw)
    (hedit:∀z:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P raw) (rawWheelSpokes π d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph Q H).neighborFinset z)).card:ℝ)≤L)
    (hext:βe*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card)
    (hhub:βh*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card):
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw:=by
  have htyped:=ordinary_physical_edit_to_typed_changes (rawWheelGraph P raw) Q (rawWheelSpokes π d raw j) H L hedit
  exact ordinary_cleanup_profile_from_deep_sample P Q F H π d X Z pR pH density tR tH L βe βh s j raw
    hpR hpR1 hpH hdensity hs hdis hmin hrows hcolumns htyped.1 htyped.2.2 htyped.2.1 hext hhub
end Oberwolfach
