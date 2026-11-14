module

public import Oberwolfach.FirstVortexConcreteUniversalMatchedOutcome
public import Oberwolfach.LongTerminalReserveSelectsClass

@[expose] public section
/-! Select the protected corrected class and retain the matching and prepared
packing arising from the same terminal reserve and sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance universalSelectedClassFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) universalSelectedClassSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_universal_matching_selected_class
    {n:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d K r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (αHost:ℝ) (hε:0≤ε) (hsmall:ε≤αHost/100000)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss:ℝ)
    (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (L e₀:ℕ)
    (hPart:∀T:SimpleGraph (Fin n),(∀v,T.degree v≤e₀)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1))⊔T).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n))
    (h:FirstVortexConcreteUniversalMatchedOutcome P π d K r Dv mm β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ βList ξPart γLoss σLoss weight w z L e₀):
    ∃D₀:MarkedReferenceDeletion P π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)),
    ∃C:Finset (Finset (Fin n)⊕(Fin n×U)),
      longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
        γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C ∧
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n) ∧
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧
    ∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
      LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2 :=by
  obtain ⟨D₀,C,hTerminal,hFor⟩:=h
  let Continuation:=fun S:SimpleGraph (Fin n)=>∃Mhost:Fin n→Fin n→ℕ,∃Del:SimpleGraph (Fin n),
    LongClassMatchingDeletionWitness Δ P π d r z (Vort.extendedVertices 1) K θ Dv a γ eps βList F hF weight w D₀ C S Mhost Del ∧
      FirstVortexClassPreparedRetainedFullPackingOutcomeWithAllHubLoad P S π Dv mm d (r+4) β ε Vort F hF θ lamAssign eps δlocal δglobal α bmatch ρ₀ ξ Δ a γ weight w z.1
        (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) z.2
  have hFor':∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξPart*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→Continuation S:=by
    intro S hSP hReg hEdit hInner hReserve
    obtain ⟨Mhost,Del,_,_,_,_,_,_,hWitness,hPrepared⟩:=hFor S hSP hReg hEdit hInner hReserve
    exact ⟨Mhost,Del,hWitness,hPrepared⟩
  obtain ⟨S,hSP,hReg,hEdit,hInner,hReserve,hContinuation⟩:=
    long_terminal_reserve_selects_corrected_class P π d r Dv mm β ε Vort αHost hε hsmall γLoss σLoss ξPart z e₀ L D₀ C hTerminal hPart Continuation hFor'
  exact ⟨D₀,C,hTerminal,S,hSP,hReg,hEdit,hInner,hReserve,hContinuation⟩
end Oberwolfach
