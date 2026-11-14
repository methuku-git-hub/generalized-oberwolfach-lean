module

public import Oberwolfach.LongInnerDualFullArcAgreement
public import Oberwolfach.MarkedPartitionedResidualHost

@[expose] public section
/-! Translate pointwise typed agreement into the exact host-encoding interface
used by the fixed-reservoir completion theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance innerResidualHostEncodingDecEq : DecidableEq V := Classical.decEq V
local instance innerResidualHostEncodingArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_inner_residual_host_encoding_agreement
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (I:Finset V)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y)
    (hSmall:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d ω).Adj x y→¬Small.Adj x y)
    (hI:∀v,π v∈I↔v∈I):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x∈I,∀y∈I,P (x,y)→(longSelectedPhysicalGraph G π d ω).Adj x y)→
    ∀T:Finset {e:V×V // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀mark a b,a∈I→b∈I→
      (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) mark a b=1 ↔
       if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
       else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b):=by
  intro P T₁ hcover T hprotect mark a b ha hb
  have hf:=long_inner_dual_full_arc_agreement G S Del Small π d ω Mhost I hphysical hcorrect hDel hSmall hcover T hprotect
  cases mark
  · simp only [Bool.false_eq_true,↓reduceIte]
    constructor
    · intro hr
      obtain ⟨e,he,hn⟩:=(hf a ha b hb).1.mpr hr
      exact ⟨⟨e,hn⟩,congrArg Prod.fst he,congrArg Prod.snd he⟩
    · rintro ⟨e,h₁,h₂⟩
      apply (hf a ha b hb).1.mp
      exact ⟨e.val,Prod.ext h₁ h₂,e.property⟩
  · simp only [Bool.true_eq_false,↓reduceIte]
    have hbπ:π b∈I:=(hI b).mpr hb
    constructor
    · intro hr
      have hr':markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true a (π.symm (π b))=1:=by simpa only [Equiv.symm_apply_apply] using hr
      obtain ⟨e,he,hm⟩:=(hf a ha (π b) hbπ).2.mpr hr'
      exact ⟨⟨e,hm⟩,congrArg Prod.fst he,by simpa only [congrArg Prod.snd he,Equiv.symm_apply_apply]⟩
    · rintro ⟨e,h₁,h₂⟩
      have h₂':e.val.val.2=π b:=by apply π.injective; simpa using congrArg π h₂
      have hr:=(hf a ha (π b) hbπ).2.mp ⟨e.val,Prod.ext h₁ h₂',e.property⟩
      simpa only [Equiv.symm_apply_apply] using hr
end Oberwolfach
