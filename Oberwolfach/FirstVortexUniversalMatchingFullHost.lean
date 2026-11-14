module

public import Oberwolfach.FirstVortexConcreteUniversalMatchedOutcome
public import Oberwolfach.LongFixedAbsorberSelectedRim
public import Oberwolfach.LongSelectedInnerClassPreservation

@[expose] public section
/-! At density one the universal correction can be evaluated on the full
host, with the reserve and matching produced on the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance universalFullHostFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) universalFullHostSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_universal_matching_full_host
    {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d K r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss:ℝ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (L e₀:ℕ)
    (hState:longPhysicalStateGraph P z.1 {0,1,2,3,4}=P)
    (hreg:P.IsRegularOfDegree (2*Fintype.card U)) (hξ:0≤ξPart)
    (h:FirstVortexConcreteUniversalMatchedOutcome P π d K r Dv mm β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss weight w z L e₀):
    ∃D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)),
      longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
        γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C ∧
    ∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C P Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P P π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 :=by
  obtain ⟨D₀,C,hTerminal,hFor⟩:=h
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
  obtain ⟨Mhost,Del,_,_,_,_,_,_,hw,hprep⟩:=hFor P le_rfl hreg hEdit hInner hRes
  exact ⟨D₀,C,hTerminal,Mhost,Del,hw,hprep⟩
end Oberwolfach
