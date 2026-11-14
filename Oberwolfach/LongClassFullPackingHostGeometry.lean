module

public import Oberwolfach.LongClassRequiredGraphProtectsReserve

@[expose] public section
/-! The class-restricted required graph is oriented by the corrected class
host and avoids the fixed selected reserve for every potential packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classFullPackingGeometryFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_class_full_packing_host_geometry
    {n d:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (G S Del Used R:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (M:Fin n→Fin n→ℕ) (I:Finset (Fin n))
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hreserve:R≤longSelectedPhysicalGraph G π d ω)
    (hDel:∀x y,R.Adj x y→¬Del.Adj x y)
    (hUsed:∀x y,Used.Adj x y→¬(longSelectedPhysicalGraph G π d ω).Adj x y):
    let Sel:=longSelectedPhysicalGraph G π d ω
    let Req:=fun x y=>M x y=1 ∧ markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack=>longClassInnerRequiredRepair S Used Kbase I Pack
    (∀Pack x y,(Kplus Pack).Adj x y→M x y=1∨M y x=1) ∧
    (∀Pack x y,(Kplus Pack).Adj x y→¬R.Adj x y):=by
  intro Sel Req Kbase Kplus
  have hbase:Kbase≤S:=by
    intro x y hk
    change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj x y at hk
    rcases hk with hi|hc
    · exact ((spanningRestriction_adj _ _ _ _).mp hi).1.1.1
    · exact hc.1
  have hsub:∀Pack,Kplus Pack≤S:=by
    intro Pack x y hk
    change (Kbase⊔spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) I).Adj x y at hk
    rcases hk with hk|he
    · exact hbase hk
    · exact ((spanningRestriction_adj _ _ _ _).mp he).1.1.1
  constructor
  · intro Pack x y hk
    have hs:=hsub Pack hk
    have hh:=hphysical x y
    rw [if_pos hs] at hh
    omega
  · intro Pack x y hk hr
    have hcorrect':=hcorrect
    have hdec:classFullPackingGeometryFin 6=instDecidableEqFin 6:=Subsingleton.elim _ _
    rw [hdec] at hcorrect'
    exact long_class_required_graph_protects_selected_reserve G S Del Used R π d ω M I Pack hphysical hcorrect' hreserve hDel hUsed x y hr hk
end Oberwolfach
