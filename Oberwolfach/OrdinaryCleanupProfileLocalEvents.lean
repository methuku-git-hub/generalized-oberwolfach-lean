module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryBoundaryLocalEvents

@[expose] public section
/-! The original common-sample cleanup profile itself supplies the parent
counts needed to add both local boundary events on a fresh physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cleanup_profile_boundary_local_probability
    (βe βh p:ℝ) (hβe:0<βe) (hβh:0<βh) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V) (Z:Finset U)
      (pR pH density tR tH L:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw→
    1-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>OrdinaryBoundaryExtensionGood Q H X βe p σ ∧ OrdinaryBoundaryHubPairGood H Z βh p σ):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_local_events_high_probability βe βh p hβe hβh hp hp1 q
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X Z pR pH density tR tH L s j raw profile
  have hc:=ordinary_boundary_parent_common_of_min_degree P X density profile.parent_min_degree
  have hp0:0≤2*density-1:=by linarith [profile.density_large]
  have hparent:=ordinary_boundary_parent_extensions_from_common_sample P Q H π d X pR pH (2*density-1)
    tR L βe profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg hp0 s j raw profile.spoke_probability
    profile.rows hc profile.rim_edit profile.spoke_column_edit profile.extension_margin
  exact hN V U hn Q H X Z hparent
end Oberwolfach
