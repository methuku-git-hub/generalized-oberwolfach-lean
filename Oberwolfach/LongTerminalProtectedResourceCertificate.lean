module

public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoad
public import Oberwolfach.LongFixedAbsorberSelectedRim
public import Oberwolfach.LongSelectedInnerClassPreservation
public import Oberwolfach.MarkedResourceRimCardinality

@[expose] public section
/-! The terminal resource gives a bounded protected graph contained in the
physical sample, suitable for the protected partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance terminalProtectedResourceCertFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) terminalProtectedResourceCertSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_protected_resource_certificate {n:ℕ} {U:Type}
    [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n)) (H:Finset U)
    (γLoss σLoss:ℝ) (e₀:ℕ) (X:Finset (Fin n)) (Z:Finset U)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 I H γLoss σLoss e₀ X Z D₀ C):
    markedResourceRimGraph C≤longPhysicalStateGraph P z.1 {0,1,2,3,4} ∧
      (markedResourceRimGraph C).edgeFinset.card≤e₀ :=by
  have hC:C.card≤e₀:=hTerminal.2.1
  have hAbs:=hTerminal.2.2.2
  have hSelected:=long_fixed_absorber_rim_is_selected P π d (r+4) z.1 false
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false C X Z hAbs
  exact ⟨hSelected.trans (long_selected_physical_subgraph_sampled_class P π d z.1),
    (marked_resource_rim_graph_edge_card_le C).trans hC⟩
end Oberwolfach
