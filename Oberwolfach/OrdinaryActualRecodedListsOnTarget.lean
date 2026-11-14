module

public import Oberwolfach.OrdinaryActualSampleForbiddenBudget
public import Oberwolfach.CandidateOrdinaryRecodedAbundanceMatchingEvent

@[expose] public section
/-! Apply the deletion-uniform recoded extending lists to the actual forbidden
graph determined by the same sample, protected reservoir and edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_recoded_lists_on_target
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Target Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (K:Finset (Sym2 (Fin n) ⊕ (Fin n×U)))
    (edit ζDel lamList:ℝ) (tret:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let F:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\F
    let Protect:=ordinaryMatchingProtect Reference Inner K
    let G:=ordinaryForbiddenRequired Target Sample Reference F Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect F Inner;
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    edit+2*Inner.card+(ordinaryResourceRows K).card+2*((3*d:ℕ):ℝ)≤ζDel*n→
    (∀Del':SimpleGraph (Fin n),(∀v,(Del'.degree v:ℝ)≤ζDel*n)→∀w,
      IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del'.Adj x y)
        (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true tret Jret w) lamList)→
    Sample\(Target\Protect)≤Del ∧ G≤Target\Protect ∧
    (∀x y,G.Adj x y→¬(Sample\Del).Adj x y) ∧
    (∀v,(G.degree v:ℝ)≤ζDel*n) ∧ (∀v,(Del.degree v:ℝ)≤ζDel*n) ∧
    (∀w,IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true tret Jret w) lamList) :=by
  intro Sample F Reference Protect G Del hEdit hBudget hLists
  have h:=ordinary_actual_sample_forbidden_matching_budget P Target Host hHost π d σ Inner Hubs K edit hEdit
  obtain ⟨hRef,hRefF,hProtect,hInner,hReserved,hDel,hG,hSep,hGdeg,hDeldeg,hrest⟩:=h
  have hBudget':edit+2*Inner.card+(letI:DecidableEq (Fin n):=Classical.decEq _; (ordinaryResourceRows K).card)+2*((3*d:ℕ):ℝ)≤ζDel*n:=by
    convert hBudget using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hGdeg':∀v,(G.degree v:ℝ)≤ζDel*n:=fun v=>(hGdeg v).trans hBudget'
  have hDeldeg':∀v,(Del.degree v:ℝ)≤ζDel*n:=fun v=>(hDeldeg v).trans hBudget'
  exact ⟨hDel,hG,hSep,hGdeg',hDeldeg',hLists Del hDeldeg'⟩
end Oberwolfach
