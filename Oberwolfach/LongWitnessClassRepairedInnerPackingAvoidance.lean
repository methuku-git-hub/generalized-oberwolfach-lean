module

public import Oberwolfach.LongWitnessSelectedRequiredAvoidance
public import Oberwolfach.LongInnerReferencePackingAvoidance
public import Oberwolfach.LongClassInnerRequiredRepair

@[expose] public section
/-! The actual old edges and an enlarged required-edge completion still avoid
every selected edge on the first protected pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance witnessClassRepairedInnerAvoidanceFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_witness_class_repaired_inner_packing_avoids_selected
    {n d r K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (G:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del Used:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ D alpha γ eps βList F hF weight w D₀ C S M Del)
    (Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))):
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>M x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))
    let Kplus:=longClassInnerRequiredRepair S Used Kbad I Pack
    (∀x∈I,∀y∈I,Sel.Adj x y→S.Adj x y)→Disjoint Sel Used→Pack⊆Used.edgeFinset→
    (∀u,Disjoint (E u) ((spanningRestriction (S\Used) I\Kplus).edgeFinset))→
    ∀x∈I,∀y∈I,Sel.Adj x y→¬(Old⊔prescribedPhysicalUnion E).Adj x y:=by
  intro Sel Req Kbad Old Kplus hClass hDis hPack hE
  have hUsed:∀x y,Sel.Adj x y→¬Used.Adj x y:=by
    intro x y hs hu
    exact (disjoint_iff_inf_le.mp hDis) ⟨hs,hu⟩
  have hK:=long_witness_required_graph_avoids_inner_selected Δ G π z I θ D alpha γ eps βList F hF weight w D₀ C S Del Used M hw
  have hKplus:∀x∈I,∀y∈I,Sel.Adj x y→¬Kplus.Adj x y:=by
    intro x hx y hy hs hk
    rcases hk with hk|he
    · exact hK x hx y hy hs hk
    · exact hUsed x y hs ((spanningRestriction_adj _ _ _ _).mp he).1.1.2
  have hPack':∀x y,Sel.Adj x y→s(x,y)∉Pack:=by
    intro x y hs hp
    exact hUsed x y hs (SimpleGraph.mem_edgeFinset.mp (hPack hp))
  apply long_inner_selected_edges_avoid_completed_packing S Sel Used Kplus I Pack E hClass hUsed hKplus hPack'
  intro u
  convert hE u using 1 <;> congr! 4 <;> exact Subsingleton.elim _ _
end Oberwolfach
