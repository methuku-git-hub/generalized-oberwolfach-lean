module

public import Oberwolfach.OrdinaryEditedReferenceFromTriangleEvent
public import Oberwolfach.OrdinaryEditedParentFromSample
public import Oberwolfach.OrdinaryTriangleReferenceJoint

@[expose] public section
/-! The combined triangle tests, both normalized cuts and the actual edit
bounds yield the edited parent on the same sample and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_edited_parent_from_common
    (d k:ℕ) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (α pstar βP ηP ηH βH c B pR pH ω βparent h ζ δ εparent L:ℝ)
    (weight:OrdinaryCycle P 3→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hω:0<ω) (hp:0<pstar) (hUlo:ω*Fintype.card V≤Fintype.card U)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hζ:0≤ζ) (hL:0≤L) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2))
    (event:ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw)
    (cuts:OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h raw coins)
    (hR:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hRow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (hscaleV:L≤ζ*Fintype.card V) (hscaleU:L≤ζ*Fintype.card U)
    (hdegree:βparent+ζ≤βH)
    (hI:8*(L+1)≤(βH-βparent)*Fintype.card V)
    (hT:5*(3:ℝ)^4*(L+1)≤(βH-βparent)*Fintype.card V)
    (hweight:ηH+8*(3:ℝ)^4*(B/(ω*pstar^(2*3-1)))*L/Fintype.card V≤εparent):
    Nonempty (OrdinaryEditedParentFields 3 (by omega) k α βparent c (B/(ω*pstar^(2*3-1))) (2*h-ζ) δ εparent P Q F H) :=by
  obtain ⟨data⟩:=ordinary_edited_reference_from_triangle_event d k hk P Q F H π α pstar βP ηP ηH βH c B pR pH
    ω βparent (2*h) ζ δ εparent L weight j raw coins hn hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ hL hQP
    hw event hR hRow hCol hscaleV hscaleU cuts.1 cuts.2 hdegree hI hT hweight
  exact ordinary_edited_parent_fields_from_sample 3 (by omega) k α βH βparent c (B/(ω*pstar^(2*3-1)))
    (2*h) ζ δ ηH εparent L P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins data
end Oberwolfach
