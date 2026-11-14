module

public import Oberwolfach.OrdinaryFixedReservoirTargetInputs
public import Oberwolfach.OrdinarySelectedMatchingFamilyResult

@[expose] public section
/-! The concrete edited target, protected absorber and matching family are
all defined from one expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryFixedTargetMatchingInputs
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin K) (rsv θ lamMatch a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamList bRate:ℝ):Prop :=
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let F:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\F
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let Abs:=ordinaryReservoirSpokeLabels Kabs
    let Protect:=ordinaryMatchingProtect Reference Inner Kabs
    let G:=ordinaryForbiddenRequired Target Sample Reference F Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect F Inner
    let Reserve:=fun u=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u
    let Lists:=fun u=>Reserve u\(Inner∪Abs u)
    let T:=ordinaryInnerSpokeTargets Inner Hubs Href;
    (∀u,Abs u⊆Reserve u) ∧
    (∀u,Disjoint (Lists u) (Abs u) ∧ Disjoint (T u) (Abs u) ∧ T u⊆Inner ∧ (T u≠∅→u∈Hubs)) ∧
    (∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤bRate*n) ∧
    Sample\(Target\Protect)≤Del ∧ G≤Target\Protect ∧
    (∀x y,G.Adj x y→¬(Sample\Del).Adj x y) ∧
    (∀v,(G.degree v:ℝ)≤bRate*n) ∧ (∀v,(Del.degree v:ℝ)≤bRate*n) ∧
    (∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y) (Lists u) (lamList/2)) ∧
    ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret),
      OrdinarySelectedMatchingFamilyResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Del σ tret Jret
end Oberwolfach
