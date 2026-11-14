module

public import Oberwolfach.OrdinaryMatchingCorrectionProductJoin
public import Oberwolfach.OrdinaryMatchingCorrectionBothLocalColumns
public import Oberwolfach.OrdinaryMatchingBalanceReservedTests

@[expose] public section
/-! The explicit matching and balance prior and the local correction bundle
can be witnessed on one expanded sample, without an independence assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_balance_corrected_witness {n qCount:ℕ}
    (P Bad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (r m t a b:ℕ) (ξ p k p₂ k₂ u pH smin σbal ζlocal:ℝ)
    (q:Fin qCount → Bool → ℝ) (s:Fin qCount → Bool → ℝ)
    (A Z Wterm:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount))
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Type}
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (Σσ,R σ)) (Ξ:Type) [Fintype Ξ] (κ:FiniteLaw Ξ)
    (E:(Σσ,R σ) → Prop)
    (Match Family:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Prop)
    (lossM lossC:ℝ):
    let Prior:=fun z:Σσ,R σ=>
      ((((E z ∧ Match z.1) ∧
        OrdinaryReferenceBalanceColumnsEvent P Bad π d pH σbal (2*((3*d:ℕ):ℝ)) z.1) ∧
        OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) ∧ Family z.1
    let Correction:=fun z:(Σσ,R σ)×Ξ=>
      (∀c:Fin 6,∀x∈Z,
        |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
          markedExpandedPhysicalProbability p k p₂ k₂ u c*(P.neighborFinset x∩Z).card|<ζlocal*Z.card) ∧
      (∀v∈Z,|rawIntervalUnassignedColumnCount π d (fun e=>z.1.1 (Sum.inr e)) v Htest-
        ∑w∈Htest,(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ)) ∧
      (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
        (Z.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ)) ∧
      OrdinaryZeroRetentionEvent π d false z.1.1 ∧
      (∀c x,|(sampledColourDegree P (fun e=>(z.1.1 (Sum.inl e)).1) c x:ℝ)-
        markedExpandedPhysicalProbability p k p₂ k₂ u c*P.degree x|<(n:ℝ)^(3/5:ℝ)) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\Bad) Bad
        (rawWheelSpokes π d raw false) A Z Wterm Bterm B;
    1-lossM ≤ μ.probability Prior → 1-lossC ≤ (μ.prod κ).probability Correction → 
    1-lossM-lossC ≤ (μ.prod κ).probability (fun z=>Prior z.1 ∧ Correction z) ∧
    (0<1-lossM-lossC → ∃z,0<(μ.prod κ).mass z ∧ Prior z.1 ∧ Correction z) :=by
  intro Prior Correction hM hC
  exact ordinary_matching_correction_product_join μ κ Prior Correction lossM lossC hM hC
end Oberwolfach
