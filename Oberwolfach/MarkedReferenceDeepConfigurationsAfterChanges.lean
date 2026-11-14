module

public import Oberwolfach.MarkedLocalConfigurationsAfterHostChange
public import Oberwolfach.MarkedLocalEstimateMonotonicity

@[expose] public section
/-! The local configuration field on the original parent domain, with the
actual coefficient margins visible. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_deep_configurations_after_changes
    (r:ℕ) (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (βC βP βA t ζ:ℝ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hDR:∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V)
    (hDS:∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀ v u,¬(H false v u∧H true v u))
    (hC:3*min βA (t/4)≤βC-(r+5:ℕ)*(ζ+ζ))
    (hP:3*min βA (t/4)≤βP-(r+7:ℕ)*ζ-(r+4:ℕ)*ζ)
    (hc:MarkedLocalConfigurationsWithSpokes r P π d Finset.univ βC βP σ H):
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) τ H' := by
  have hh:=marked_local_configurations_after_host_change r P π d βC βP ζ σ τ H H' FR FS
    hRim hSpoke hDR hDS htypes hc
  exact markedLocalConfigurations_mono r P π d Finset.univ _ _ _ _ hC hP τ H' hh
end Oberwolfach
