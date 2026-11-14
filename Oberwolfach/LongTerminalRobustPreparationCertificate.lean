module

public import Oberwolfach.LongTerminalProtectedResourceCertificate
public import Oberwolfach.GroupedRegularClassExtraction

@[expose] public section
/-! Turn a uniform fixed-sample factor continuation into the protected-graph
interface required by the regular partition, retaining the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance terminalRobustPrepFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) terminalRobustPrepSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem long_terminal_robust_preparation_certificate {n:ℕ} {U:Type}
    [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n)) (Hubs:Finset U)
    (γLoss σLoss:ℝ) (e₀:ℕ) (X:Finset (Fin n)) (Z:Finset U)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (ξ:ℝ) (q:ℕ) (F:Fin q→SimpleGraph (Fin n))
    (hTerminal:longTerminalProtectedReserve P π d r z z.2 I Hubs γLoss σLoss e₀ X Z D₀ C)
    (hRobust:∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
      (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
      markedResourceRimGraph C≤S→HasFactorDecomposition S F):
    ∃A:SimpleGraph (Fin n),A≤longPhysicalStateGraph P z.1 {0,1,2,3,4} ∧ A.edgeFinset.card≤e₀ ∧
      ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*Fintype.card U)→A≤S→
        (∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)→
        (∀v,((Finset.univ.filter (fun y=>Xor (S.Adj v y) ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj v y))).card:ℝ)≤ξ*n)→
        HasFactorDecomposition S F :=by
  obtain ⟨hsub,hcard⟩:=long_terminal_protected_resource_certificate P π d r z I Hubs γLoss σLoss e₀ X Z D₀ C hTerminal
  refine ⟨markedResourceRimGraph C,hsub,hcard,?_⟩
  intro S hSP hreg hA hInside hXor
  apply hRobust S hSP hreg _ hInside hA
  intro v
  rw [changed_neighbourhoods_eq_xor]
  exact hXor v
end Oberwolfach
