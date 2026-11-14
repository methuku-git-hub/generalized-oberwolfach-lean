module

public import Oberwolfach.OrdinaryCombinedTriangleEvent
public import Oberwolfach.OrdinaryEditedParentFields
public import Oberwolfach.OrdinaryFullHostSeedBounds

@[expose] public section
/-! Instantiate the edited-parent reference data using the original named
triangle sample event and its fixed cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_edited_reference_from_triangle_event
    (d k:ℕ) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (α pstar βP ηP ηH βH c B pR pH ω βparent h ζ δ εparent L:ℝ)
    (weight:OrdinaryCycle P 3→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hω:0<ω) (hp:0<pstar) (hUlo:ω*Fintype.card V≤Fintype.card U)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hζ:0≤ζ) (hL:0≤L) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(3-2))
    (event:ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw)
    (hR:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hRow:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hCol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (hscaleV:L≤ζ*Fintype.card V) (hscaleU:L≤ζ*Fintype.card U)
    (hcutR:BipartiteLargeCut (sampledOrientation (rawWheelGraph P raw\F) coins) δ h)
    (hcutS:BipartiteLargeCut (relationMultiplicity (rawWheelSpokes π d raw j)) δ h)
    (hdegree:βparent+ζ≤βH)
    (hI:8*(L+1)≤(βH-βparent)*Fintype.card V)
    (hT:5*(3:ℝ)^4*(L+1)≤(βH-βparent)*Fintype.card V)
    (hweight:ηH+8*(3:ℝ)^4*(B/(ω*pstar^(2*3-1)))*L/Fintype.card V≤εparent):
    Nonempty (OrdinaryEditedSampleReferenceData 3 (by omega) k α βH βparent c (B/(ω*pstar^(2*3-1))) h ζ δ
      ηH εparent L P Q F (rawWheelSpokes π d raw j) H (fun e=>raw (Sum.inl e)) coins):=by
  let seed:=ordinaryFullHostSeed (U:=U) P F 3 weight pR pH
  have hseed:∀W,c/(Fintype.card V:ℝ)^(3-1)≤seed W ∧
      seed W≤(B/(ω*pstar^(2*3-1)))/(Fintype.card V:ℝ)^(3-1):=by
    intro W
    exact ordinaryFullHostSeed_bounds P F 3 (by omega) weight pR pH ω pstar c B hn hu hω hp hUlo hUhi
      hRlo hRhi hHlo hHhi hc hB hw W
  have hBseed:0≤B/(ω*pstar^(2*3-1)):=by positivity
  have hs:∀v,βH*Fintype.card V≤((Finset.univ.filter (rawWheelSpokes π d raw j v)).card:ℝ):=by
    intro v
    simpa only [Fintype.card_subtype] using event.1.1 v
  refine ⟨⟨hn,hu,hUhi,hk,hζ,hc,hBseed,hL,hQP,?_,hRow,hCol,hscaleV,hscaleU,?_,hcutS,
    hs,hdegree,?_,?_,hI,hT,seed,hseed,?_,?_,hweight⟩⟩
  · simpa only [rawWheelGraph] using hR
  · simpa only [rawWheelGraph] using hcutR
  · intro x y hxy hf
    exact event.1.2.2.1 x y hxy hf
  · intro v u u' hne
    exact event.1.2.2.2 v u u' hne
  · intro x y hxy hf
    simpa only [rawWheelGraph] using event.1.2.1.1 x y hxy hf
  · intro v u
    simpa only [rawWheelGraph] using event.1.2.1.2 v u
end Oberwolfach
