module

public import Oberwolfach.LongClassRequiredInnerResidualCoverage
public import Oberwolfach.LongInnerResidualHostEncodingAgreement

@[expose] public section
/-! The exact fixed-reservoir inner-host interface follows from actual
coverage by the old packing and enlarged required graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance classRequiredInnerHostEncodingDecEq : DecidableEq V := Classical.decEq V
local instance classRequiredInnerHostEncodingArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_class_required_inner_host_encoding
    (G S Del Small Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (I:Finset V) (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hDel:∀x∈I,∀y∈I,¬Del.Adj x y)
    (hSmall:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d ω).Adj x y→¬Small.Adj x y)
    (hI:∀v,π v∈I↔v∈I) (hPack:Pack⊆Used.edgeFinset)
    (hUsedSel:∀x y,Used.Adj x y→¬(longSelectedPhysicalGraph G π d ω).Adj x y):
    let Sel:=longSelectedPhysicalGraph G π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x y,s(x,y)∈Pack→x≠y→Small.Adj x y)→Kplus≤Small→
    ∀T:Finset {e:V×V // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀mark a b,a∈I→b∈I→
      (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) mark a b=1 ↔
       if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
       else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b):=by
  intro Sel K Old Kplus P T₁ hOld hK T hprotect
  have hcover:=long_class_required_inner_residual_coverage S Sel Used Small π d I D Pack M hphysical hPack hUsedSel hOld hK
  exact long_inner_residual_host_encoding_agreement G S Del Small π d ω M I hphysical hcorrect hDel hSmall hI hcover T hprotect
end Oberwolfach
