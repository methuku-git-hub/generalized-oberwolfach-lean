module

public import Oberwolfach.LongActualCorrectionBeforeProtectedClassMatching
public import Oberwolfach.InducedFractionalCycles
public import Oberwolfach.MarkedValidDeletionPhysicalDegree
public import Oberwolfach.MarkedResourceRimGraphContinuation
public import Oberwolfach.LongActualValidDeletionProtectedOrientationMatching

@[expose] public section
/-! Use the correction first, then a protected class and its orientation,
and finally obtain matching and lists after one compatible deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance validReserveOrientationFin (n:ℕ):DecidableEq (Fin n):=fun a b=>Classical.propDecidable (a=b)
theorem long_actual_valid_deletion_reserved_orientation_matching
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass δ:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (W:Finset U)
    (K B:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ):
    let V:=Fin n
    let ω:=z.1
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false)) z.2 false false
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del;
    ∀ D₀:MarkedReferenceDeletion P π d σ,
    D₀.Valid H (r+4) T W (γLoss*n) (σLoss*n)→
    (∀Del:SimpleGraph V,(∀v,(Del.degree v:ℝ)≤Δ*n)→Matching Del)→
    γLoss+ξClass+δ≤Δ→
    (∀A:SimpleGraph V,(∀v,A.degree v≤B)→
      ∃S:SimpleGraph V,S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
        ∃M:V→V→ℕ,(∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
          (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
          (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
          (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y))→
    ∀C:Finset (Finset V⊕(V×U)),C.card≤B→Disjoint D₀.removed C→
      let A:=markedResourceRimGraph C;
      ∃S:SimpleGraph V,S≤P ∧ S.IsRegularOfDegree (2*Fintype.card U) ∧
        (∀x y,((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y→
          (S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)) ∧
        (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n) ∧
        ∃M:V→V→ℕ,(∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
          (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
          (∀v,((orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).degree v:ℝ)≤δ*n) ∧
          (∀x y,(orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M).Adj x y→¬((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y) ∧
        ∀Kbad:SimpleGraph V,Kbad≤S→
          ∃Del:SimpleGraph V,(markedSampleArcSetGraph P π d σ D₀.arcs)≤Del ∧
            ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
            orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
            (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
            (∀x y,Del.Adj x y→¬((spanningRestriction (⊤:SimpleGraph V) T)⊔A).Adj x y) ∧
            (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
            (∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧ (∀x y,M x y=1→P.Adj x y) ∧
            (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧ Matching Del := by
  intro V ω σ H Matching D₀ hvalid hMatching hsum hOrientation C hcard hdis A
  have hLate:=long_actual_valid_deletion_protected_orientation_matching Δ P π d r γLoss σLoss ξClass δ z T W K B θ D alpha γ eps βList F hF weight w
    D₀ hvalid hMatching hsum hOrientation
  exact hLate (markedResourceRimGraph C) (fun v=>(markedResourceRimGraph_degree_le C v).trans hcard)
    (markedReferenceDeletion_disjoint_resourceRimGraph P π d σ D₀ C hdis)
end Oberwolfach
