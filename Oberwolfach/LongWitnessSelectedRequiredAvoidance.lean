module

public import Oberwolfach.LongSelectedCloseIsMarked
public import Oberwolfach.LongSelectedCloseRequiredAvoidance
public import Oberwolfach.LongWitnessInnerMarkedDirection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_witness_required_graph_avoids_inner_selected
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let RMark:=fun x y=>markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)=1
    let Req:=fun x y=>M x y=1 ∧ ¬RMark x y
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d T Req (fun x y=>Used.Adj x y)
    ∀x∈T,∀y∈T,Sel.Adj x y→¬Kbad.Adj x y:=by
  intro Sel RMark Req Kbad x hx y hy hSel hK
  have hc:=long_selected_close_required_avoids_reference S Sel Used T π d M RMark
    (fun x y hs hclose=>long_selected_close_edge_has_marked_direction G π d z.1 x y hs hclose)
    (long_matching_witness_preserves_inner_marked_direction Δ G π z T θ D alpha γ eps βList F hF weight w D₀ C S Del M hw) hw.1
  change (spanningRestriction ((S\Used)\Sel) T ⊔ longCloseRequiredGraph S π d Req (fun x y=>Used.Adj x y)).Adj x y at hK
  rcases hK with h|h
  · have hh:((S\Used)\Sel).Adj x y:=(spanningRestriction_adj _ _ _ _).mp h |>.1
    exact hh.2 hSel
  · exact hc x hx y hy hSel h
end Oberwolfach
