module

public import Oberwolfach.OrdinaryEditedParentFields

@[expose] public section
/-! Build all edited-parent cut, degree, configuration and weight fields
from one original sample and the displayed symmetric-edit bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_edited_parent_fields_from_sample
    (r:ℕ) (hr:3≤r) (k:ℕ) (α βsource β b B h ζ δ εsource ε d:ℝ)
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (σ coins:Sym2 V→Bool)
    (data:OrdinaryEditedSampleReferenceData r hr k α βsource β b B h ζ δ εsource ε d P Q F H₀ H σ coins):
    Nonempty (OrdinaryEditedParentFields r hr k α β b B (h-ζ) δ ε P Q F H):=by
  have hQF:Disjoint Q F:=by
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    exact (data.graph_sub hxy.1).2 hxy.2
  have hcuts:=ordinary_edited_cuts_from_sample (retainedGraph P σ) Q F H₀ H coins δ h ζ d
    data.positive_V data.positive_U data.zeta_nonneg hQF data.rim_scale data.spoke_scale
    data.rim_edit data.spoke_row_edit data.spoke_column_edit data.rim_cut data.spoke_cut
  have hcounts:=ordinary_edited_configuration_counts_from_sample P Q F H₀ H r k hr data.k_lower
    (max (1/2) (cycleThreshold r)) (α/4) βsource β d σ data.positive_V data.hub_upper data.edit_nonneg
    data.graph_sub data.isolator_potential data.transfer_potential data.rim_edit data.spoke_row_edit
    data.spoke_column_edit data.isolator_margin data.transfer_margin
  have hdeg:=ordinary_edited_spoke_degree_from_sample H₀ H βsource β ζ d data.sampled_spoke_degree
    data.spoke_row_edit data.rim_scale data.degree_margin
  have hedit:=ordinary_conflict_free_edit_bounds (retainedGraph P σ) Q F H₀ H d hQF data.rim_edit
    data.spoke_row_edit data.spoke_column_edit
  obtain ⟨w,hw,hR,hS⟩:=ordinary_edited_parent_weight_from_potential P (retainedGraph P σ\F) Q F H₀ H r
    (by omega) data.positive_V data.hub_upper data.seed b B εsource ε d data.bound_nonneg data.upper_nonneg
    data.edit_nonneg (data.graph_sub.trans sdiff_le) data.seed_bounds hedit.1 hedit.2.1 hedit.2.2
    (fun x y hxy=>data.rim_potential x y (data.graph_sub hxy).1 (data.graph_sub hxy).2)
    (fun v u _=>data.spoke_potential v u) data.weight_margin
  exact ⟨⟨sampledOrientation Q coins,hcuts.1,hcuts.2.1,hcuts.2.2,hdeg,hcounts.1,hcounts.2,w,hw,hR,hS⟩⟩
end Oberwolfach
