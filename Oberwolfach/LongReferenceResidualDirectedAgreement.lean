module

public import Oberwolfach.LongReferenceResidualTypedAgreement
public import Oberwolfach.LongDualResidualRawEncoding

@[expose] public section
/-! Directed agreement on a shared physical edge away from deletion and retyping. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance directedAgreementDecEq : DecidableEq V := Classical.decEq V
local instance directedAgreementArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_reference_residual_directed_agreement
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del):
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∀T:Finset {e:V×V // P e}, ∀x y,
      (longSelectedPhysicalGraph G π d ω).Adj x y→(S\Small).Adj x y→
      ¬Del.Adj x y→¬(physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).Adj x y→
      (markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) false x y=1 ↔
         ∃e:residualOrdinaryArc P T,e.val.val=(x,y)) ∧
      (markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) true x (π.symm y)=1 ↔
         ∃e:residualMarkedArc P T,e.val.val=(x,y)):=by
  intro P T₁ T x y hSel hNow hDel hChange
  have hs:M x y+M y x=1:=by simpa only [if_pos hNow.1] using hphysical x y
  by_cases hm:M x y=1
  · let e:{a:V×V // P a}:=⟨(x,y),⟨hm,hNow.2,by simp⟩⟩
    have hpoint:=long_dual_reference_agreement_away_changes G S Del Small π d ω M hphysical hcorrect T e hSel hDel hChange
    constructor
    · constructor
      · intro h
        exact ⟨⟨e,hpoint.1.mpr h⟩,rfl⟩
      · rintro ⟨z,hz⟩
        have he:z.val=e:=Subtype.ext hz
        exact hpoint.1.mp (he ▸ z.property)
    · constructor
      · intro h
        exact ⟨⟨e,hpoint.2.mpr h⟩,rfl⟩
      · rintro ⟨z,hz⟩
        have he:z.val=e:=Subtype.ext hz
        exact hpoint.2.mp (he ▸ z.property)
  · have hmy:M y x=1:=by omega
    have hrev:=long_selected_no_reverse_away_deletion G S Del π d ω M hphysical hcorrect y x hmy (fun h=>hDel h.symm)
    constructor
    · constructor
      · intro h; exact False.elim (hrev.1 h)
      · rintro ⟨z,hz⟩
        apply False.elim
        apply hm
        simpa only [hz] using z.val.property.1
    · constructor
      · intro h; exact False.elim (hrev.2 (by simpa only [Equiv.symm_apply_apply] using h))
      · rintro ⟨z,hz⟩
        apply False.elim
        apply hm
        simpa only [hz] using z.val.property.1
end Oberwolfach
