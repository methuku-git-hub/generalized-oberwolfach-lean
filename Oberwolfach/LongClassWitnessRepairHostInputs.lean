module

public import Oberwolfach.LongClassRepairHostOrientation
public import Oberwolfach.LongClassRequiredGraphProtectsReserve
public import Oberwolfach.LongMatchingWitnessCorrection

@[expose] public section
/-! The same class correction witness supplies the free and prescribed
orientations needed by the reserve-avoiding host completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classWitnessRepairHostInputsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) classWitnessRepairHostInputsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem long_class_matching_witness_repair_host_inputs
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hUsed:Disjoint (longSelectedPhysicalGraph G π d z.1) Used):
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>M x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack;
    (∀x y,rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y→¬Del.Adj x y→M x y=1) ∧
    (∀Pack x y,(Kplus Pack).Adj x y→M x y=1∨M y x=1) ∧
    (∀Pack x y,(Kplus Pack).Adj x y→¬(markedResourceRimGraph C).Adj x y):=by
  intro Sel Req Kbase Kplus
  have hc:=long_matching_witness_correction_bound Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del M hw
  have hDel:∀x y,(markedResourceRimGraph C).Adj x y→¬Del.Adj x y:=by
    intro x y hr hd
    exact (hw.2.2.2.2.2.2.1 x y hd) (Or.inr hr)
  have hUsed':∀x y,Used.Adj x y→¬Sel.Adj x y:=by
    intro x y hu hs
    exact (disjoint_iff_inf_le.mp hUsed) ⟨hs,hu⟩
  refine ⟨hw.2.2.2.2.2.2.2.1,?_,?_⟩
  · exact long_class_required_repair_oriented S Sel Used π d I Req M hw.1
  · intro Pack x y hk hr
    exact long_class_required_graph_protects_selected_reserve G S Del Used (markedResourceRimGraph C) π d z.1 M I Pack
      hw.1 hc.1 hreserve hDel hUsed' x y hr hk
end Oberwolfach
