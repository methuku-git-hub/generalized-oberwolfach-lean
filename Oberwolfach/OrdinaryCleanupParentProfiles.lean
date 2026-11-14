module

public import Oberwolfach.OrdinaryBoundaryCleanupCountsFromSamples

@[expose] public section
/-! The original common sample and bounded edits needed by ordinary cleanup,
packaged as a proposition for the selected earlier outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure OrdinaryCleanupParentProfiles (P Q F:SimpleGraph V) (H:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color):Prop where
  rim_nonneg:0≤pR
  rim_le_one:pR≤1
  spoke_nonneg:0≤pH
  density_large:1/2≤density
  spoke_probability:∀u,s u j=pH
  forbidden_disjoint:Disjoint Q F
  parent_min_degree:∀v,density*X.card≤((X∩P.neighborFinset v).card:ℝ)
  rows:RawOrdinaryRows P π d 2 X pR s j tR raw
  columns:RawOrdinaryDomainIndices F π d 3 Z pH j tH raw
  rim_edit:∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L
  spoke_column_edit:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
    (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L
  spoke_row_edit:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v))
    (Finset.univ.filter (H v))).card:ℝ)≤L
  extension_margin:βe*Fintype.card (V⊕U)+tR+3*L≤pR^2*pH*(2*density-1)*X.card
  hub_margin:βh*Fintype.card (V⊕U)+tH+2*L≤pH^2*Z.card
end Oberwolfach
