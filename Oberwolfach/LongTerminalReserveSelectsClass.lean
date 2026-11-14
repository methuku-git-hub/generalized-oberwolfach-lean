module

public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoad
public import Oberwolfach.LongProtectedRegularClassSelection
public import Oberwolfach.LongFirstVortexProtectionGraph
public import Oberwolfach.LongFixedAbsorberSelectedRim
public import Oberwolfach.LongSelectedInnerClassPreservation

@[expose] public section
/-! Choose the corrected class using the actual terminal reserve, retaining
any continuation proved uniformly for every admissible class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance terminalSelectFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) terminalSelectFinSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_terminal_reserve_selects_corrected_class
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r Dv mm:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (αHost:ℝ) (hε:0≤ε) (hsmall:ε≤αHost/100000)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (e₀ L:ℕ) (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 (Vort.extendedVertices 1) (Vort.extendedIndices 1)
      γLoss σLoss e₀ (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) D₀ C)
    (hPart:∀T:SimpleGraph (Fin n),(∀v,T.degree v≤e₀)→
      ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1))⊔T).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n))
    (Continuation:SimpleGraph (Fin n)→Prop)
    (hFor:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→Continuation S):
    ∃S:SimpleGraph (Fin n),S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
      (∀x∈Vort.extendedVertices 1,∀y∈Vort.extendedVertices 1,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y) ∧
      markedResourceRimGraph C≤S ∧ Continuation S :=by
  have hInner:= (long_first_vortex_protection_graph P Dv mm β ε αHost Vort hε hsmall).2
  have hA:∀v,(markedResourceRimGraph C).degree v≤e₀:=by
    intro v
    exact (markedResourceRimGraph_degree_le C v).trans hTerminal.2.1
  have hSample:markedResourceRimGraph C≤longPhysicalStateGraph P z.1 {0,1,2,3,4}:=by
    have hh:=long_fixed_absorber_rim_is_selected P π d (r+4) z.1 false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false C
      (Vort.extendedVertices (L+1)) (Vort.extendedIndices (L+1)) hTerminal.2.2.2
    exact hh.trans (long_selected_physical_subgraph_sampled_class P π d z.1)
  obtain ⟨S,hSP,hreg,hedit,hinner,hreserve⟩:=long_protected_regular_class_selection P
    (longPhysicalStateGraph P z.1 {0,1,2,3,4})
    (spanningRestriction (⊤:SimpleGraph (Fin n)) (Vort.extendedVertices 1)) (markedResourceRimGraph C)
    (Vort.extendedVertices 1) (Fintype.card U) e₀ ξClass hInner hA hSample hPart
  exact ⟨S,hSP,hreg,hedit,hinner,hreserve,hFor S hSP hreg hedit hinner hreserve⟩
end Oberwolfach
