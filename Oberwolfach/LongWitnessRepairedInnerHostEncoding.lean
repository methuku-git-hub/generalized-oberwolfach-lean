module

public import Oberwolfach.LongWitnessRepairedInnerPackingAvoidance
public import Oberwolfach.LongRequiredInnerHostEncoding

@[expose] public section
/-! The actual old and prescribed packing yields the fixed-reservoir inner
host interface for the same class correction and matching witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance witnessRepairedHostEncodingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) witnessRepairedHostEncodingSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance witnessRepairedHostEncodingArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _

theorem long_witness_repaired_inner_host_encoding
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n)))
    (hI:∀v,π v∈I↔v∈I):
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>M x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))
    let Kplus:=Kbad⊔spanningRestriction (Used\Old) I
    let Small:=Old⊔prescribedPhysicalUnion E
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>z.1 (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    (∀x∈I,∀y∈I,Sel.Adj x y→S.Adj x y)→Disjoint Sel Used→Pack⊆Used.edgeFinset→
    (∀u,Disjoint (E u) ((spanningRestriction (S\Used) I\Kplus).edgeFinset))→
    Kplus.edgeFinset⊆Finset.univ.biUnion E→
    ∀T:Finset {e:(Fin n×Fin n) // P e},(∀e,e.val.1∈I→(e∈T↔e∈T₁))→
    ∀mark a b,a∈I→b∈I→
      (markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) mark a b=1 ↔
       if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
       else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b):=by
  intro Sel Req Kbad Old Kplus Small P T₁ hclass hdis hPack hE hcover T hprotect
  have hcorrect:orientationDisagreementGraph (longPhysicalStateGraph G z.1 {0,1,2,3,4}) (fun e=>(z.1 (Sum.inl e)).2) M≤Del:=
    (long_matching_witness_correction_bound Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del M hw).1
  have hDel:∀x∈I,∀y∈I,¬Del.Adj x y:=by
    intro x hx y hy hd
    have hxy:x≠y:=hd.ne
    have hZ:(spanningRestriction (⊤:SimpleGraph (Fin n)) I).Adj x y:=by
      simp only [spanningRestriction_adj,SimpleGraph.top_adj]
      exact ⟨hxy,hx,hy⟩
    exact (hw.2.2.2.2.2.2.1 x y hd) (Or.inl hZ)
  have hSmall:∀x∈I,∀y∈I,Sel.Adj x y→¬Small.Adj x y:=
    long_witness_repaired_inner_packing_avoids_selected Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Used M hw Pack E hclass hdis hPack hE
  have hUsed:∀x y,Used.Adj x y→¬Sel.Adj x y:=by
    intro x y hu hs
    exact (disjoint_iff_inf_le.mp hdis) ⟨hs,hu⟩
  have hOld:∀x y,s(x,y)∈Pack→x≠y→Small.Adj x y:=by
    intro x y hp hxy
    exact Or.inl ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨hp,hxy⟩)
  have hK:Kplus≤Small:=by
    intro x y hk
    have he:s(x,y)∈Finset.univ.biUnion E:=hcover (SimpleGraph.mem_edgeFinset.mpr hk)
    exact Or.inr ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨he,hk.ne⟩)
  exact long_required_inner_host_encoding G S Del Small Used π d z.1 M I Req Pack hw.1 hcorrect hDel hSmall hI hPack hUsed hOld hK T hprotect
end Oberwolfach
