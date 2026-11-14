module

public import Oberwolfach.OrdinaryUnreservedGeometryNumbers
public import Oberwolfach.OrdinarySameSampleBalanceProfiles

@[expose] public section
/-! The original common row and hub-domain sample, bounded edits, and the
same fresh reserve discharge the non-numeric reserve-geometry fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_unreserved_geometry_from_common_sample
    (r k d:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε pR pH tR tH e L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (π:Equiv.Perm V)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (num:OrdinaryUnreservedGeometryNumbers r k ω βparent β b B εparent εstar η ξ ζ p ε (e+tR+2*tH+3*L) X Z)
    (htR:0≤tR) (htH:0≤tH) (he:0≤e) (hL:0≤L)
    (hrows:RawOrdinaryRows P π d 2 X pR s j tR raw)
    (hcols:RawOrdinaryDomainIndices F π d 3 Z pH j tH raw)
    (hparent:∀v,|pR*(P.neighborFinset v∩X).card-2*pH*Z.card|≤e)
    (hrim:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hspoke:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ):
    OrdinaryUnreservedGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε
      (e+tR+2*tH+3*L) (e+tR+2*tH+3*L) Q F H X Z σ:=by
  have hrim':∀v,((changed (Q.neighborFinset v) ((rawWheelGraph P raw).neighborFinset v)).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using hrim v
  have hspoke':∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d raw j v))).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using hspoke v
  have hp:=ordinary_same_sample_balance_profiles P F Q H π d X Z pR pH tR tH e L htR htH he hL
    s j raw hrows hcols hparent hrim' hspoke'
  apply ordinary_unreserved_geometry_from_balance_profiles r k ω βparent β b B εparent εstar η ξ ζ p ε
    (e+tR+2*tH+3*L) Q F H X Z σ num hbal hp.2
  · intro v _
    exact hp.1 v
  · exact hgood
end Oberwolfach
