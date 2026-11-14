module

public import Oberwolfach.LongInnerSelectedTypedDirection
public import Oberwolfach.LongDualReferenceTypeAgreement

@[expose] public section
/-! Once the actual packing covers every nonselected inner edge, the corrected
residual has exactly the reference typed directions on that inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance innerDualTypedAgreementDecEq : DecidableEq V := Classical.decEq V
local instance innerDualTypedAgreementArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_inner_dual_typed_agreement
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (I:Finset V)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y):
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x∈I,∀y∈I,P (x,y)→(longSelectedPhysicalGraph G π d ω).Adj x y)→
    ∀T:Finset {e:V×V // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀e:{a:V×V // P a},e.val.1∈I→e.val.2∈I→
      (e∉T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) false e.val.1 e.val.2=1) ∧
      (e∈T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) true e.val.1 (π.symm e.val.2)=1):=by
  intro P T₁ hcover T hprotect e hx hy
  have hagree:=long_dual_initial_agrees_with_selected_types G Small π d (fun a=>ω (Sum.inl a)) Mhost e
  have heq:=hprotect e hx
  have hdir:=long_inner_selected_typed_direction G S Del π d ω Mhost I hphysical hcorrect hDel
    e.val.1 hx e.val.2 hy (hcover e.val.1 hx e.val.2 hy e.property) e.property.1
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
