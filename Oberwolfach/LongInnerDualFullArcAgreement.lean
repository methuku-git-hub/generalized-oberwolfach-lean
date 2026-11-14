module

public import Oberwolfach.LongInnerDualTypedAgreement

@[expose] public section
/-! Pointwise, both directions of the inner agreement, including selected
arcs regarded as elements of the actual corrected residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance innerDualFullArcAgreementDecEq : DecidableEq V := Classical.decEq V
local instance innerDualFullArcAgreementArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_inner_dual_full_arc_agreement
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (I:Finset V)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y)
    (hSmall:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d ω).Adj x y→¬Small.Adj x y):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x∈I,∀y∈I,P (x,y)→(longSelectedPhysicalGraph G π d ω).Adj x y)→
    ∀T:Finset {e:V×V // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀x∈I,∀y∈I,
      ((∃e:{a:V×V // P a},e.val=(x,y) ∧ e∉T)↔
        markedPhysicalRim G π (3*d) (fun a=>markedExpandedPhysicalCollapse (ω (Sum.inl a))) false x y=1) ∧
      ((∃e:{a:V×V // P a},e.val=(x,y) ∧ e∈T)↔
        markedPhysicalRim G π (3*d) (fun a=>markedExpandedPhysicalCollapse (ω (Sum.inl a))) true x (π.symm y)=1):=by
  intro P T₁ hcover T hprotect x hx y hy
  have hsurvive:=long_inner_selected_typed_arcs_survive_residual G Del Small π d ω Mhost I hcorrect hDel hSmall x hx y hy
  have hagree:=long_inner_dual_typed_agreement G S Del Small π d ω Mhost I hphysical hcorrect hDel hcover T hprotect
  constructor
  · constructor
    · rintro ⟨e,he,hn⟩
      have heq:=(hagree e (by simpa only [he] using hx) (by simpa only [he] using hy)).1.mp hn
      simpa only [he] using heq
    · intro hr
      let e:{a:V×V // P a}:=⟨(x,y),hsurvive.1 hr⟩
      exact ⟨e,rfl,(hagree e hx hy).1.mpr hr⟩
  · constructor
    · rintro ⟨e,he,hm⟩
      have heq:=(hagree e (by simpa only [he] using hx) (by simpa only [he] using hy)).2.mp hm
      simpa only [he] using heq
    · intro hr
      let e:{a:V×V // P a}:=⟨(x,y),hsurvive.2 hr⟩
      exact ⟨e,rfl,(hagree e hx hy).2.mpr hr⟩
end Oberwolfach
