module

public import Oberwolfach.LongSelectedTypedDirectionAwayDeletion
public import Oberwolfach.LongDualReferenceTypeAgreement
public import Oberwolfach.MarkedIndegreeFinsetInterface

@[expose] public section
/-! A common physical edge keeps its selected ordinary/marked type away from
the actual orientation deletion and the actual type-correction graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance dualReferenceAwayDecEq : DecidableEq V := Classical.decEq V
local instance dualReferenceAwayArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_dual_reference_agreement_away_changes
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∀T:Finset {e:V×V // P e},∀e:{a:V×V // P a},
      (longSelectedPhysicalGraph G π d ω).Adj e.val.1 e.val.2→¬Del.Adj e.val.1 e.val.2→
      ¬(physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).Adj e.val.1 e.val.2→
      (e∉T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) false e.val.1 e.val.2=1) ∧
      (e∈T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) true e.val.1 (π.symm e.val.2)=1):=by
  intro P T₁ T e hSel hDel hchange
  have heq:e∈T↔e∈T₁:=by
    by_contra hn
    have hdiff:e∈symmDiff T T₁:=by
      simp only [Finset.mem_symmDiff]
      tauto
    apply hchange
    refine ⟨hSel.ne,Finset.mem_image.mpr ⟨e,?_,rfl⟩⟩
    convert hdiff using 1 <;> congr!
  have hagree:=long_dual_initial_agrees_with_selected_types G Small π d (fun a=>ω (Sum.inl a)) Mhost e
  have hdir:=long_selected_typed_direction_away_from_deletion G S Del π d ω Mhost hphysical hcorrect
    e.val.1 e.val.2 hSel hDel e.property.1
  have hOrd:markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) false e.val.1 e.val.2=1→e∉T:=by
    intro h hm
    exact hagree.1 h (heq.mp hm)
  have hMark:markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) true e.val.1 (π.symm e.val.2)=1→e∈T:=by
    intro h
    exact heq.mpr (hagree.2 h)
  constructor
  · constructor
    · intro hn
      rcases hdir with h|h
      · exact h
      · exact False.elim (hn (hMark h))
    · exact hOrd
  · constructor
    · intro hm
      rcases hdir with h|h
      · exact False.elim (hOrd h hm)
      · exact h
    · exact hMark
end Oberwolfach
