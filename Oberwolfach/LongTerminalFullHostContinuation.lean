module

public import Oberwolfach.FirstVortexUniversalMatchingFullHost

@[expose] public section
/-! Evaluate any universal corrected-class continuation on the full host
when the sampled class equals that host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance terminalFullHostFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) terminalFullHostSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_full_host_continuation
    {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (ξPart γLoss σLoss:ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (L e₀:ℕ)
    (D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C)
    (hState:longPhysicalStateGraph P z.1 {0,1,2,3,4}=P)
    (hreg:P.IsRegularOfDegree (2*Fintype.card U)) (hξ:0≤ξPart)
    (Continuation:SimpleGraph (Fin n)→Prop)
    (hFor:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→Continuation S):
    Continuation P :=by
  have hRes0:=long_fixed_absorber_rim_is_selected P π d (r+4) z.1 false
    (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 false C
    (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) hTerminal.2.2.2
  have hRes:markedResourceRimGraph C≤P:=by
    apply hRes0.trans
    simpa only [hState] using (long_selected_physical_subgraph_sampled_class P π d z.1)
  have hEdit:∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (P.neighborFinset v)).card:ℝ)≤ξPart*n:=by
    intro v
    rw [hState]
    simp only [changed,Finset.sdiff_self,Finset.union_empty,Finset.card_empty,Nat.cast_zero]
    positivity
  have hInner:∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,P.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y:=by
    intro x hx y hy
    rw [hState]
  exact hFor P le_rfl hreg hEdit hInner hRes
end Oberwolfach
