module

public import Oberwolfach.OrdinaryTriangleParentRootScaleChoice
public import Oberwolfach.OrdinaryTriangleEditedParentScaled
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! A single physical edit bound and the preselected scale produce the
general edited parent on the same outcome and orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_edited_parent_physical_at_scale
    (d k:ℕ) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (α pstar βP ηP ηH βH c B pR pH ω βparent h ζ δ εparent rate L:ℝ) (N₀:ℕ)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B ω pstar βparent εparent ζ rate N₀)
    (weight:OrdinaryCycle P 3→ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (hN:N₀≤Fintype.card V) (hN₀:1≤N₀) (hu:0<Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hω:0<ω) (hp:0<pstar) (hUlo:ω*Fintype.card V≤Fintype.card U)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hζ:0≤ζ) (hL:0≤L) (hLrate:L≤rate*Fintype.card V) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2))
    (event:ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw)
    (cuts:OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h raw coins)
    (hphysical:∀z:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P raw) (rawWheelSpokes π d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph Q H).neighborFinset z)).card:ℝ)≤L):
    Nonempty (OrdinaryEditedParentFields 3 (by omega) k α βparent c (B/(ω*pstar^(2*3-1))) (2*h-ζ) δ εparent P Q F H) :=by
  have hn:0<Fintype.card V:=by omega
  have hNr:(N₀:ℝ)≤Fintype.card V:=by exact_mod_cast hN
  obtain ⟨hscaleV,hscaleU,hI,hT,hweight⟩:=hscale.2 (Fintype.card V) (Fintype.card U) L hNr hUlo hL hLrate
  obtain ⟨hR,hRow,hCol⟩:=ordinary_physical_edit_to_typed_changes (rawWheelGraph P raw) Q (rawWheelSpokes π d raw j) H L hphysical
  exact ordinary_triangle_edited_parent_from_common d k hk P Q F H π α pstar βP ηP ηH βH c B pR pH
    ω βparent h ζ δ εparent L weight j raw coins hn hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ hL hQP
    hw event cuts hR hRow hCol hscaleV hscaleU hscale.1 hI hT hweight
end Oberwolfach
