module

public import Oberwolfach.OrdinaryActualSampleForbiddenBudget
public import Oberwolfach.OrdinaryTwoDeletionTargetSurvival
public import Oberwolfach.OrdinaryLostEdgesEditDegree

@[expose] public section
/-! Use the genuinely lost edges for matching, and a separate larger
completion deletion to protect the chosen reference and absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_two_deletion_inputs
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S Host:SimpleGraph (Fin n)) (hHost:Host≤P) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (K:Finset (Sym2 (Fin n)⊕(Fin n×U))) (edit:ℝ):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
    let Protect:=ordinaryMatchingProtect Reference Inner K
    let DelMatch:=Sample\S
    let DelFinish:=ordinaryForbiddenSampleDeletion Sample S Reference Protect Bad Inner
    let Budget:ℝ:=edit+2*Inner.card+(ordinaryResourceRows K).card+2*((3*d:ℕ):ℝ);
    (∀v,((Finset.univ.filter (fun w=>Xor (S.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    (∀v,(DelMatch.degree v:ℝ)≤edit) ∧ (∀v,(DelFinish.degree v:ℝ)≤Budget) ∧
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) DelMatch.edgeFinset) x y→(S\Protect).Adj x y) ∧
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→
      ¬DelFinish.Adj x y→(S\Protect).Adj x y) :=by
  intro Sample Bad Reference Protect DelMatch DelFinish Budget hEdit
  have hbase:=ordinary_actual_sample_forbidden_matching_budget P S Host hHost π d σ Inner Hubs K edit hEdit
  obtain ⟨hRef,hBad,hProtect,hInner,hRim,hFinish,hG,hSep,hGdeg,hDeldeg,hrest⟩:=hbase
  have hProtect0:Protect≤longPhysicalStateGraph P σ {0}:=by
    have hh:Reference≤longPhysicalStateGraph P σ {0}:=by
      dsimp [Reference]
      rw [←ordinary_shared_sample_reference_graph_eq_state_zero P σ]
      exact sdiff_le
    exact hProtect.trans hh
  have hsurvive:=ordinary_two_deletion_target_survival P S Host Protect DelMatch DelFinish hHost π d σ hProtect0 le_rfl hFinish
  have hLost:=lost_graph_degree_le_symmetric_edit S Sample edit hEdit
  refine ⟨?_,?_,?_,?_⟩
  · intro v;convert hLost v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro v;convert hDeldeg v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro x y hArc
    apply hsurvive.1 x y
    convert hArc using 1 <;> congr! 12
  · convert hsurvive.2 using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
