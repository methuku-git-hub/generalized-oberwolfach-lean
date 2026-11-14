module

public import Oberwolfach.MarkedCommonConfigurationMonotonicity

@[expose] public section
/-! Common marked configurations are monotone under inclusion of both
typed rims and both typed spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_common_configurations_under_host_inclusion
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (β ζ:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hRim:∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1→
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1)
    (hH:∀ mark v u,H mark v u→H' mark v u)
    (hc:MarkedCommonConfigurationsWithSpokes r P π d β ζ σ H):
    MarkedCommonConfigurationsWithSpokes r P π d β ζ τ H' :=by
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
  let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
  let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
  let tail:=fun e:E=>e.val.1
  let head:=fun e:E=>e.val.2
  let ktail:=fun e:K=>e.val.1
  let khead:=fun e:K=>e.val.2
  let tail':=fun e:E'=>e.val.1
  let head':=fun e:E'=>e.val.2
  let ktail':=fun e:K'=>e.val.1
  let khead':=fun e:K'=>e.val.2
  have hE:∀ e:E,∃ e':E',tail' e'=tail e∧head' e'=head e:=by
    intro e
    exact ⟨⟨e.val,hRim false e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  have hK:∀ e:K,∃ e':K',ktail' e'=ktail e∧khead' e'=khead e:=by
    intro e
    exact ⟨⟨e.val,hRim true e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  constructor
  · intro C hC
    exact (hc.1 C hC).trans (by exact_mod_cast Finset.card_le_card (potentialMarkedHubs_mono H' H hH C))
  constructor
  · intro u hu
    let F:=marked_common_cycle_host_inclusion tail head ktail khead tail' head' ktail' khead' π (3*d) H H' hE hK hH (r+4) (u 0) (u 1)
    have hh:Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ H u)≤
        Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) τ H' u):=Fintype.card_le_of_injective F F.injective
    exact (hc.2.1 u hu).trans (by exact_mod_cast hh)
  · intro v v' hv u hu j
    let F:=marked_common_path_host_inclusion tail head ktail khead tail' head' ktail' khead' π (3*d) H H' hE hK hH (r+3+1) j v v' (u 0) (u 1)
    have hh:Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ H u j v v')≤
        Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) τ H' u j v v'):=Fintype.card_le_of_injective F F.injective
    exact (hc.2.2 v v' hv u hu j).trans (by exact_mod_cast hh)
end Oberwolfach
