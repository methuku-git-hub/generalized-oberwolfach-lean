module

public import Oberwolfach.OrdinaryReservedSpokeExtending
public import Oberwolfach.RawExpandedReservedPairsProbability

@[expose] public section
/-! The selected two-path, reserved-spoke neighbourhood and reserved-pair
counts needed by ordinary completion, all on one expanded outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryReservedCompletionTests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ) (p smin:ℝ) (s:U→Bool→ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    (∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false v y)).card:ℝ)) ∧
    (∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>σ (Sum.inr e)) w false
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>σ (Sum.inl e)) i).card*s w false|<(n:ℝ)^(3/4:ℝ)) ∧
    ∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ)
end Oberwolfach
