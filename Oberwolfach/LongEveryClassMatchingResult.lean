module

public import Oberwolfach.LongActualValidDeletionEveryClass
public import Oberwolfach.LongClassProtectedCorrectionUniformSpacing
public import Oberwolfach.LongFirstVortexProtectedUnionBudget
public import Oberwolfach.MarkedValidDeletionPhysicalDegree
public import Oberwolfach.MarkedResourceRimGraph
public import Oberwolfach.LongReservedRimContainedInClass
public import Oberwolfach.LongSelectedInnerClassPreservation
public import Oberwolfach.LongEarlyMatchingListsForDeletion
public import Oberwolfach.LongActualRawLawParameters

@[expose] public section

/-! Once the correction and absorber reserve are fixed, every regular class
with the prescribed edit and protection conditions admits the same-sample
balanced orientation and a matching-compatible deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 80000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance everyClassResultFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def LongEveryClassMatchingResult
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (γLoss σLoss ξClass:ℝ) (z:MarkedExpandedActualOutcome (U:=U) π d)
    (T:Finset (Fin n)) (K:ℕ) (θ D alpha γ eps βList:ℝ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) : Prop :=
    let V:=Fin n
    let ω:=z.1
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let Z:=spanningRestriction (⊤:SimpleGraph V) T
    let A:=markedResourceRimGraph C
    let Matching:=fun Del:SimpleGraph V=>LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps Δ βList P π F hF weight w z T Del;
    ∀S:SimpleGraph V,S≤P→S.IsRegularOfDegree (2*Fintype.card U)→
      (∀v,((changed ((longPhysicalStateGraph P ω {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξClass*n)→
      (∀x∈T,∀y∈T,S.Adj x y↔(longPhysicalStateGraph P ω {0,1,2,3,4}).Adj x y)→
      A≤S→
      (∀x∈T,∀y∈T,(longSelectedPhysicalGraph P π d ω).Adj x y→S.Adj x y) ∧
      ∃M:V→V→ℕ,∃Del:SimpleGraph V,
        (∀x y,M x y+M y x=if S.Adj x y then 1 else 0) ∧
        (∀v,(∑w,M v w)=Fintype.card U ∧ (∑w,M w v)=Fintype.card U) ∧
        (markedSampleArcSetGraph P π d raw D₀.arcs)≤Del ∧
        ((longPhysicalStateGraph P ω {0,1,2,3,4})\S)≤Del ∧
        orientationDisagreementGraph (longPhysicalStateGraph P ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del ∧
        (∀v,(Del.degree v:ℝ)≤Δ*n) ∧
        (∀x y,Del.Adj x y→¬(Z⊔A).Adj x y) ∧
        (∀x y,rawSelectedPhysicalRelation P π d (fun e=>ω (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
        (∀Kbad:SimpleGraph V,Kbad≤S→∀x y,Kbad.Adj x y→M x y=1 ∨ M y x=1) ∧
        (∀x y,M x y=1→P.Adj x y) ∧
        (∀x y,rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (ω e)) x y→¬Del.Adj x y→M x y=1) ∧ Matching Del
end Oberwolfach
