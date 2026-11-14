module

public import Oberwolfach.OrdinaryFixedTargetMatchingInputs
public import Oberwolfach.OrdinarySelectedPostDemandColumnTargetResult
public import Oberwolfach.OrdinaryEmptyRetentionOutcome

@[expose] public section
/-! Matching and completion use separate deletions; the forced graph is
chosen only after the coherent matching package family is fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryFixedPostmatchingColumnInputs
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin K) (rsv θ lamMatch a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamList bRate z δplace:ℝ):Prop :=
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=longPhysicalStateGraph P σ {0}\Bad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let Abs:=ordinaryReservoirSpokeLabels Kabs
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let DelMatch:=Sample\Target
    let DelFinish:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner
    let Reserve:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u
    let Lists:=fun u=>Reserve u\(Inner∪Abs u)
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    (∀u,Abs u⊆Reserve u) ∧
    (∀u,Disjoint (Lists u) (Abs u) ∧ Disjoint (T u) (Abs u) ∧ T u⊆Inner ∧ (T u≠∅→u∈Hubs)) ∧
    (∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤bRate*n) ∧
    (∀x y,rawMixedPhysicalArc (ordinaryEligibleHost P π d) π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset) x y→
        (Target\Protect).Adj x y) ∧
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→
      ¬DelFinish.Adj x y→(Target\Protect).Adj x y) ∧
    (∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelFinish.Adj x y)
      (Lists u) (lamList/2)) ∧
    OrdinarySelectedPostDemandColumnTargetResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π
      P DelMatch Target Protect Bad Inner Hubs bRate z δplace σ 0 J
end Oberwolfach
