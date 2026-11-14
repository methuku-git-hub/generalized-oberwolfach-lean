module

public import Oberwolfach.MarkedCorrectionThenReserve

@[expose] public section
/-! A reserve selected in the corrected host consists of resources that
remain after the correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_corrected_reserve_subset_remaining
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (D₀:MarkedReferenceDeletion P π d σ)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (habs:MarkedFixedTerminalAbsorber P π d m
      (rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)) Reserve X Z):
    Reserve⊆D₀.remaining H:=by
  have hs:=(marked_fixed_terminal_absorber_supported_in_host P π d m
    (rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset)
    (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)) Reserve X Z habs).2
  have heq:=marked_deleted_sample_resources P π d σ H D₀.arcs D₀.spokes
  rw [heq] at hs
  exact hs
end Oberwolfach
