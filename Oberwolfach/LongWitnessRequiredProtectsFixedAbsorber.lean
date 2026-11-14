module

public import Oberwolfach.LongRequiredGraphProtectsReserve
public import Oberwolfach.LongMatchingWitnessCorrection

@[expose] public section
/-! The enlarged first-vortex required graph avoids the very same fixed
absorber protected by the class matching and correction witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance witnessProtectsFixedAbsorberFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_matching_witness_required_protects_fixed_absorber
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) t)
    (X:Finset (Fin n)) (Z:Finset U) (Pack:Finset (Sym2 (Fin n))):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false t J false false
    MarkedFixedTerminalAbsorber G π d (r+4) raw H C X Z→
    Disjoint (longSelectedPhysicalGraph G π d z.1) Used→
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let RMark:=fun x y=>markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)=1
    let Req:=fun x y=>M x y=1 ∧ ¬RMark x y
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))
    let Kplus:=Kbad⊔spanningRestriction (Used\Old) I
    ∀x y,(markedResourceRimGraph C).Adj x y→¬Kplus.Adj x y:=by
  intro raw H habs hdis Sel RMark Req Kbad Old Kplus
  have hC:markedResourceRimGraph C≤Sel:=
    long_fixed_absorber_rim_is_selected G π d (r+4) z.1 false t J false C X Z habs
  have hDel:∀x y,(markedResourceRimGraph C).Adj x y→¬Del.Adj x y:=by
    intro x y hC hD
    have hh:=hw.2.2.2.2.2.2.1 x y hD
    exact hh (Or.inr hC)
  have hUsed:∀x y,Used.Adj x y→¬Sel.Adj x y:=by
    intro x y hu hs
    exact (disjoint_iff_inf_le.mp hdis) ⟨hs,hu⟩
  exact long_required_graph_protects_selected_reserve G S Del Used (markedResourceRimGraph C) π d z.1 M I Pack
    hw.1 (long_matching_witness_correction_bound Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del M hw).1 hC hDel hUsed
end Oberwolfach
