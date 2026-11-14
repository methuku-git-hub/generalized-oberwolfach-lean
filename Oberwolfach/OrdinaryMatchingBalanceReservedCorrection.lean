module

public import Oberwolfach.OrdinaryMatchingCorrectionProductJoin
public import Oberwolfach.OrdinaryMatchingBalanceBoundary
public import Oberwolfach.OrdinaryReservedCompletionTests
public import Oberwolfach.OrdinarySameSampleConstructedReservoirEarlyGeometry

@[expose] public section
/-! The matching, reference balance and reserved-completion tests coexist with
the corrected reservoir on one expanded outcome and its correction coin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_balance_reserved_correction_join
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P F:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r m t a b:ℕ)
    (θ c assign errDel lamList rsv σ ξ p smin:ℝ) (j:Bool)
    (q:U→Bool→ℝ) (s:U→Bool→ℝ)
    (Core:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Prop)
    (A Z Wterm:Finset (Fin n)) (Bterm B:Finset U)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)]
    (μ:FiniteLaw (Σω,R ω)) (κ:FiniteLaw (Sym2 (Fin n)→Bool))
    (E:(Σω,R ω)→Prop) (εM εC:ℝ)
    (hM:1-εM≤μ.probability (fun z=>
      (((E z ∧ OrdinaryRecodedMatchingExtra P π d θ c q s assign errDel lamList Core z.1) ∧
        OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
        OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1))
    (hC:1-εC≤(μ.prod κ).probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B)):
    let All:=fun z:(Σω,R ω)×(Sym2 (Fin n)→Bool)=>
      ((((E z.1 ∧ OrdinaryRecodedMatchingExtra P π d θ c q s assign errDel lamList Core z.1.1) ∧
        OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1.1) ∧
        OrdinaryBoundaryStartEvent π d z.1.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1.1) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B;
    1-εM-εC≤(μ.prod κ).probability All ∧
      (0<1-εM-εC→∃z,0<(μ.prod κ).mass z ∧ All z) :=by
  intro All
  exact ordinary_matching_correction_product_join μ κ _ _ εM εC hM hC
end Oberwolfach
