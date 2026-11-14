module

public import Oberwolfach.OrdinarySampledSurvivalTarget
public import Oberwolfach.OrdinaryApproximateArcAvoidReferenceHost

@[expose] public section
/-! The approximate matching only deletes lost sample edges. The later
selected-layer completion may use a larger deletion protecting the reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_two_deletion_target_survival
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S Host Protect DelMatch DelFinish:SimpleGraph (Fin n)) (hHost:Host≤P)
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hProtect:Protect≤longPhysicalStateGraph P σ {0})
    (hMatch:longPhysicalStateGraph P σ {0,1,2,3,4}\S≤DelMatch)
    (hFinish:longPhysicalStateGraph P σ {0,1,2,3,4}\(S\Protect)≤DelFinish):
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset) x y→(S\Protect).Adj x y) ∧
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→
      ¬DelFinish.Adj x y→(S\Protect).Adj x y) :=by
  have hM:=ordinary_sampled_survival_in_target P S Host DelMatch hHost π d σ hMatch
  have hF:=ordinary_sampled_survival_in_target P (S\Protect) Host DelFinish hHost π d σ hFinish
  constructor
  · intro x y harc
    refine ⟨hM.2 x y harc,?_⟩
    intro hp
    have hh:=ordinary_approximate_arc_avoids_reference_host Host P DelMatch π d σ x y harc
    exact hh.2 (hProtect hp)
  · intro x y hsel hdel
    exact hF.1 x y hsel hdel
end Oberwolfach
