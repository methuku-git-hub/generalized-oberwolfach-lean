module

public import Oberwolfach.LongReferenceResidualTypedGraphs
public import Oberwolfach.LongSelectedNoReverseAwayDeletion

@[expose] public section
/-! On every common physical edge away from the same deletion and retyping
changes, the selected and corrected residual types coincide. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance referenceResidualAgreementDecEq : DecidableEq V := Classical.decEq V
local instance referenceResidualAgreementArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_reference_residual_typed_agreement
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del):
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∀T:Finset {e:V×V // P e},∀mark:Bool,∀x y,
      (longSelectedPhysicalGraph G π d ω).Adj x y→(S\Small).Adj x y→
      ¬(Del⊔physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).Adj x y→
      ((longReferenceTypedGraph G π d ω mark).Adj x y↔(longResidualTypedGraph S Small M T mark).Adj x y):=by
  intro P T₁ T mark x y hSel hNow hExcept
  have hDel:¬Del.Adj x y:=fun h=>hExcept (Or.inl h)
  have hChange:¬(physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).Adj x y:=fun h=>hExcept (Or.inr h)
  have oriented:∀a b,(longSelectedPhysicalGraph G π d ω).Adj a b→(S\Small).Adj a b→
      ¬Del.Adj a b→¬(physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).Adj a b→M a b=1→
      ((longReferenceTypedGraph G π d ω mark).Adj a b↔(longResidualTypedGraph S Small M T mark).Adj a b):=by
    intro a b hs hn hd hc hm
    let e:{z:V×V // P z}:=⟨(a,b),⟨hm,hn.2,by simp⟩⟩
    have hr: M b a≠1:=by
      intro h
      have hp:=hphysical a b
      split_ifs at hp <;> omega
    have hu:∀z:{z:V×V // P z},(z.val=(a,b)∨z.val=(b,a))→z=e:=by
      intro z hz
      rcases hz with hz|hz
      · apply Subtype.ext
        exact hz
      · have hrev:M b a=1:=by simpa only [hz] using z.property.1
        exact False.elim (hr hrev)
    have hpoint:=long_dual_reference_agreement_away_changes G S Del Small π d ω M hphysical hcorrect T e hs hd hc
    have hrev:=long_selected_no_reverse_away_deletion G S Del π d ω M hphysical hcorrect a b hm hd
    cases mark with
    | false =>
      constructor
      · intro h
        have hraw:markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) false a b=1:=by
          rcases h.2 with h|h
          · exact h
          · exact False.elim (hrev.1 h)
        exact ⟨hn,e,Or.inl rfl,hpoint.1.mpr hraw⟩
      · rintro ⟨_,z,hz,hzT⟩
        have heq:=hu z hz
        subst z
        exact ⟨hs,Or.inl (hpoint.1.mp hzT)⟩
    | true =>
      constructor
      · intro h
        have hraw:markedPhysicalRim G π (3*d) (fun z=>markedExpandedPhysicalCollapse (ω (Sum.inl z))) true a (π.symm b)=1:=by
          rcases h.2 with h|h
          · exact h
          · exact False.elim (hrev.2 h)
        exact ⟨hn,e,Or.inl rfl,hpoint.2.mpr hraw⟩
      · rintro ⟨_,z,hz,hzT⟩
        have heq:=hu z hz
        subst z
        exact ⟨hs,Or.inl (hpoint.2.mp hzT)⟩
  have hsum:M x y+M y x=1:=by simpa only [if_pos hNow.1] using hphysical x y
  have hdir:M x y=1∨M y x=1:=by omega
  rcases hdir with h|h
  · exact oriented x y hSel hNow hDel hChange h
  · have he:=oriented y x hSel.symm hNow.symm (fun h=>hDel h.symm) (fun h=>hChange h.symm) h
    constructor <;> intro hh
    · exact (he.mp hh.symm).symm
    · exact (he.mpr hh.symm).symm
end Oberwolfach
