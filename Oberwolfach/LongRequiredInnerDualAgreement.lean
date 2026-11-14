module

public import Oberwolfach.LongRequiredInnerCoverageRepair
public import Oberwolfach.LongInnerDualTypedAgreement

@[expose] public section
/-! If the enlarged required graph and the old edges are actually packed,
the corrected residual agrees with the selected typed sample on the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance requiredInnerDualAgreementDecEq : DecidableEq V := Classical.decEq V
local instance requiredInnerDualAgreementArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_required_inner_dual_agreement
    (G S Del Small Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Mhost:V→V→ℕ) (I:Finset V) (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) Mhost≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y)
    (hPack:Pack⊆Used.edgeFinset)
    (hUsedSel:∀x y,Used.Adj x y→¬(longSelectedPhysicalGraph G π d ω).Adj x y):
    let Sel:=longSelectedPhysicalGraph G π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Kplus:=K⊔spanningRestriction (Used\Old) I
    let P:=longEligibleResidualArc Mhost Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x y,s(x,y)∈Pack→x≠y→Small.Adj x y)→Kplus≤Small→
    ∀T:Finset {e:V×V // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀e:{a:V×V // P a},e.val.1∈I→e.val.2∈I→
      (e∉T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) false e.val.1 e.val.2=1) ∧
      (e∈T↔markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (ω (Sum.inl x))) true e.val.1 (π.symm e.val.2)=1):=by
  intro Sel K Old Kplus P T₁ hOld hK T hprotect
  have hrepair:=long_required_inner_coverage_repair S Sel Used π d I D Pack hPack hUsedSel
  have hcover:∀x∈I,∀y∈I,P (x,y)→Sel.Adj x y:=by
    intro x hx y hy hp
    have hm:Mhost x y=1:=hp.1
    have hs:S.Adj x y:=by
      by_contra hn
      have hh:=hphysical x y
      simp only [hn,if_false] at hh
      omega
    by_contra hn
    have hnotPack:s(x,y)∉Pack:=by
      intro h
      exact hp.2.1 (hOld x y h hs.ne)
    exact hp.2.1 (hK (hrepair.2.2.1 x y hx hy hs hn hnotPack))
  exact long_inner_dual_typed_agreement G S Del Small π d ω Mhost I hphysical hcorrect hDel hcover T hprotect
end Oberwolfach
