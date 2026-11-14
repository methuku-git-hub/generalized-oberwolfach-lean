module

public import Oberwolfach.OrdinaryEditedReferenceFromTriangleEvent
public import Oberwolfach.OrdinaryTriangleReferenceJoint
public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! The same common profile and normalized reference cuts supply the edited
triangle reference data after bounded rim and spoke changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_edited_reference_from_common_profile
    (d k:ℕ) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (A:Finset V) (Z:Finset U)
    (α pstar βP ηP ηH βH c B pR pH ω βparent href ζ δ εparent L density tR tH βe βh:ℝ)
    (weight:OrdinaryCycle P 3→ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hω:0<ω) (hp:0<pstar) (hUlo:ω*Fintype.card V≤Fintype.card U)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hζ:0≤ζ) (hL:0≤L) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2))
    (event:ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j raw)
    (cuts:OrdinaryTriangleReferenceNormalizedCuts P F π d j δ href raw coins)
    (hscaleV:L≤ζ*Fintype.card V) (hscaleU:L≤ζ*Fintype.card U)
    (hdegree:βparent+ζ≤βH)
    (hI:8*(L+1)≤(βH-βparent)*Fintype.card V)
    (hT:5*(3:ℝ)^4*(L+1)≤(βH-βparent)*Fintype.card V)
    (hweight:ηH+8*(3:ℝ)^4*(B/(ω*pstar^(2*3-1)))*L/Fintype.card V≤εparent):
    Nonempty (OrdinaryEditedSampleReferenceData 3 (by omega) k α βH βparent c (B/(ω*pstar^(2*3-1))) (2*href) ζ δ
      ηH εparent L P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins) := by
  exact ordinary_edited_reference_from_triangle_event d k hk P Q F H π α pstar βP ηP ηH βH c B pR pH ω βparent
    (2*href) ζ δ εparent L weight j raw coins hn hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ hL hQP hw event
    profile.rim_edit profile.spoke_row_edit profile.spoke_column_edit hscaleV hscaleU cuts.1 cuts.2 hdegree hI hT hweight
end Oberwolfach
