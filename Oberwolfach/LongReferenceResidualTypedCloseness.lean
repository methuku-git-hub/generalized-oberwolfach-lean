module

public import Oberwolfach.LongReferenceResidualTypedAgreement
public import Oberwolfach.TypedPhysicalChangeDegree

@[expose] public section
/-! The physical edit bound and the actual correction/deletion bounds give
separate ordinary and marked physical-neighbourhood edit bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance referenceResidualTypedCloseDecEq : DecidableEq V := Classical.decEq V
local instance referenceResidualTypedCloseArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_reference_residual_typed_closeness
    (G S Del Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (η δ χ:ℝ)
    (hPhys:∀x,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset x) ((S\Small).neighborFinset x)).card:ℝ)≤η)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
    ∀T:Finset {e:V×V // P e},
    (∀x,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree x:ℝ)≤χ)→
    ∀mark x,((changed ((longReferenceTypedGraph G π d ω mark).neighborFinset x)
      ((longResidualTypedGraph S Small M T mark).neighborFinset x)).card:ℝ)≤η+δ+χ:=by
  intro P T₁ T hChange mark x
  let Retype:=physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)
  have hRetype:(((Del⊔Retype).degree x):ℝ)≤δ+χ:=by
    have hn:(Del⊔Retype).degree x≤Del.degree x+Retype.degree x:=by
      convert graph_degree_sup_le Del Retype x using 1 <;> congr!
    have hr:(((Del⊔Retype).degree x):ℝ)≤(Del.degree x:ℝ)+Retype.degree x:=by exact_mod_cast hn
    linarith [hDel x,hChange x]
  have hagree:=long_reference_residual_typed_agreement G S Del Small π d ω M hphysical hcorrect T mark
  have hh:=typed_change_degree_from_physical_and_retyping
    (longSelectedPhysicalGraph G π d ω) (S\Small)
    (longReferenceTypedGraph G π d ω mark) (longResidualTypedGraph S Small M T mark) (Del⊔Retype)
    (long_reference_typed_subgraph G π d ω mark) (long_residual_typed_subgraph S Small M T mark)
    hagree x η (δ+χ) (by convert hPhys x using 1 <;> congr!) (by convert hRetype using 1 <;> congr!)
  linarith
end Oberwolfach
