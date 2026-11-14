module

public import Oberwolfach.LongFixedAbsorberSelectedRim
public import Oberwolfach.LongSelectedCloseIsMarked
public import Oberwolfach.LongSelectedMarkedOrientationPreserved
public import Oberwolfach.LongSelectedTypedRawDirection
public import Oberwolfach.LongRequiredInnerCoverageRepair

@[expose] public section
/-! The class orientation preserves the fixed absorber.  Consequently neither
the original required graph nor the unembedded-used repair consumes its rims. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance requiredProtectsReserveDecEq : DecidableEq V := Classical.decEq V

theorem long_required_graph_protects_selected_reserve
    (G S Del Used R:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (M:V→V→ℕ) (I:Finset V) (Pack:Finset (Sym2 V))
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G ω {0,1,2,3,4}) (fun e=>(ω (Sum.inl e)).2) M≤Del)
    (hreserve:R≤longSelectedPhysicalGraph G π d ω)
    (hDel:∀x y,R.Adj x y→¬Del.Adj x y)
    (hUsed:∀x y,Used.Adj x y→¬(longSelectedPhysicalGraph G π d ω).Adj x y):
    let Sel:=longSelectedPhysicalGraph G π d ω
    let RMark:=fun x y=>markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1
    let Req:=fun x y=>M x y=1 ∧ ¬RMark x y
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Kplus:=K⊔spanningRestriction (Used\Old) I
    ∀x y,R.Adj x y→¬Kplus.Adj x y:=by
  intro Sel RMark Req K Old Kplus x y hr hk
  have hSel:Sel.Adj x y:=hreserve hr
  change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y) ⊔ spanningRestriction (Used\Old) I).Adj x y at hk
  rcases hk with (hi|hc)|he
  · exact ((spanningRestriction_adj _ _ _ _).mp hi).1.2 hSel
  · obtain ⟨hs,hclose,hreq⟩:=hc
    have hmark:=long_selected_close_edge_has_marked_direction G π d ω x y hSel hclose
    have hmxy:RMark x y→M x y=1:=by
      intro hm
      have hraw:=long_selected_marked_raw_direction G π d (fun e=>ω (Sum.inl e)) x y hm
      exact long_selected_marked_direction_preserved G Del ω M hcorrect x y hraw.1 (hDel x y hr)
    have hmyx:RMark y x→M y x=1:=by
      intro hm
      have hraw:=long_selected_marked_raw_direction G π d (fun e=>ω (Sum.inl e)) y x hm
      exact long_selected_marked_direction_preserved G Del ω M hcorrect y x hraw.1 (hDel y x hr.symm)
    rcases hmark with hm|hm
    · have hM:=hmxy hm
      rcases hreq with hreq|hreq
      · exact hreq.1.2 hm
      · have hh:=hphysical x y
        rw [if_pos hs,hM,hreq.1.1] at hh
        omega
    · have hM:=hmyx hm
      rcases hreq with hreq|hreq
      · have hh:=hphysical x y
        rw [if_pos hs,hreq.1.1,hM] at hh
        omega
      · exact hreq.1.2 hm
  · exact hUsed x y ((spanningRestriction_adj _ _ _ _).mp he).1.1 hSel
end Oberwolfach
