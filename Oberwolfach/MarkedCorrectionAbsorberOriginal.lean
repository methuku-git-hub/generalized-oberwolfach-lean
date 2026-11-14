module

public import Oberwolfach.MarkedFixedAbsorberProtectedLift
public import Oberwolfach.MarkedDeletionReservedGraphs

@[expose] public section
/-! The reserve selected after a protected correction is also a fixed
absorber in the original sample on every terminal pair inside the protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_correction_absorber_fixed_original
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D:MarkedReferenceDeletion P π d σ)
    (Reserve:Finset (Finset V⊕(V×U))) (I X:Finset V) (J Z:Finset U)
    (hI:∀v,π v∈I↔v∈I) (hXI:X⊆I) (hZJ:Z⊆J)
    (hCovered:D.removed.filter (markedInnerResource I J)=∅)
    (habs:MarkedFixedTerminalAbsorber P π d m
      (rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D.spokes)) Reserve X Z):
    MarkedFixedTerminalAbsorber P π d m σ H Reserve X Z :=by
  have hgraphs:=marked_reference_deletion_reserved_graphs P π d σ D
  apply marked_fixed_absorber_protected_deletion_lift P π d m σ H D.removed Reserve I X J Z hI hXI hZJ hCovered
  change MarkedFixedTerminalAbsorber P π d m
    (rawMarkedDeleteRims σ (physicalEdgeGraph (markedReservedRimPairs D.removed)).edgeFinset)
    (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (markedReservedSpokePairs D.removed))) Reserve X Z
  rw [hgraphs.1,hgraphs.2]
  exact habs
end Oberwolfach
