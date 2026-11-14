module

public import Oberwolfach.CandidateOrdinaryRecodedAbundanceMatchingEvent

@[expose] public section
/-! A named form of the matching, occupancy, assignments and extending-list
conditions selected together by the recoded abundance event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryRecodedMatchingExtra
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ) (θ c:ℝ)
    (q s:U→Bool→ℝ) (a ζDel lamList:ℝ)
    (Core:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Prop)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    Core σ ∧
    (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>σ (Sum.inr e)) v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
    (∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>σ (Sum.inr e)) w
        (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) ∧
    OrdinaryUnassignedPairsStartsEvent π d (θ/2) q σ ∧ OrdinaryProtectedBadEdgeAssignments π d σ a ∧
    ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
      (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
      IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true tret Jret w) lamList
end Oberwolfach
