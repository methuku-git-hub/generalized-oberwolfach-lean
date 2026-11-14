module

public import Oberwolfach.OrdinaryFixedPostmatchingInputs
public import Oberwolfach.OrdinaryActualTwoDeletionInputs

@[expose] public section
/-! An original symmetric edit supplies the target-survival conditions for
both deletions while retaining the selected post-matching family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_postmatching_inputs_from_edit
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F₀:U→SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F₀ u).ConnectedComponent) (i₀:Fin K) (rsv θ lamMatch a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Target:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamList bRate edit:ℝ):
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
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit) →
    (∀u,Abs u⊆Reserve u) →
    (∀u,Disjoint (Lists u) (Abs u) ∧ Disjoint (T u) (Abs u) ∧ T u⊆Inner ∧ (T u≠∅→u∈Hubs)) →
    (∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤bRate*n) →
    (∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelFinish.Adj x y)
      (Lists u) (lamList/2)) →
    OrdinarySelectedMatchingFamilyPostDemandResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π
      P DelMatch Target Protect Bad Inner bRate σ 0 J →
    OrdinaryFixedPostmatchingInputs F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Target σ Inner Hubs Kabs lamList bRate :=by
  intro Sample Bad Reference Href Abs Protect DelMatch DelFinish Reserve Lists T J hEdit hAbsSub havoid hAbs hext hfamily
  have hHost:ordinaryEligibleHost P π d≤P:=by intro x y h;exact h.1
  have hsurvive:=ordinary_actual_two_deletion_inputs P Target (ordinaryEligibleHost P π d) hHost π d σ Inner Hubs Kabs edit hEdit
  rw [ordinary_shared_sample_reference_graph_eq_state_zero P σ] at hsurvive
  unfold OrdinaryFixedPostmatchingInputs
  refine ⟨hAbsSub,havoid,hAbs,?_,?_,hext,hfamily⟩
  · convert hsurvive.2.2.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hsurvive.2.2.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
