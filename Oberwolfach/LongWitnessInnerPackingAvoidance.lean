module

public import Oberwolfach.LongWitnessSelectedRequiredAvoidance
public import Oberwolfach.LongInnerReferencePackingAvoidance
public import Oberwolfach.PhysicalSamplingLayerDisjoint

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_witness_inner_selected_edges_avoid_packing
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
    let Req:=fun x y=>M x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) true x (π.symm y)≠1
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d T Req (fun x y=>Used.Adj x y)
    ∀(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))),
    (∀x∈T,∀y∈T,Sel.Adj x y→S.Adj x y)→Disjoint Sel Used→
    Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset→
    (∀u,Disjoint (E u) ((spanningRestriction (S\Used) T\Kbad).edgeFinset))→
    ∀x∈T,∀y∈T,Sel.Adj x y→
      ¬(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E).Adj x y:=by
  intro Sel Req Kbad Pack E hClass hUsed hPack hE
  have hK:=long_witness_required_graph_avoids_inner_selected Δ G π z T θ D alpha γ eps βList F hF weight w D₀ C S Del Used M hw
  have hUsed':∀x y,Sel.Adj x y→¬Used.Adj x y:=by
    intro x y hSel hU
    exact (disjoint_iff_inf_le.mp hUsed) ⟨hSel,hU⟩
  have hPack':∀x y,Sel.Adj x y→s(x,y)∉Pack:=by
    intro x y hSel hmem
    have he:=hPack hmem
    have hApprox:(longApproximatePhysicalGraph G π d z.1).Adj x y:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    exact (disjoint_iff_inf_le.mp (selected_and_approximate_rim_graphs_disjoint G π d z.1)) ⟨hSel,hApprox⟩
  have hh:=long_inner_selected_edges_avoid_completed_packing S Sel Used Kbad T Pack E hClass hUsed' hK hPack'
    (by
      intro u
      apply Finset.disjoint_left.mpr
      intro e he hJ
      apply Finset.disjoint_left.mp (hE u) he
      simpa only [SimpleGraph.mem_edgeFinset] using hJ)
  intro x hx y hy hs hSmall
  apply hh x hx y hy hs
  rcases hSmall with hOld|hNew
  · exact Or.inl hOld
  · apply Or.inr
    simpa only [prescribedPhysicalUnion,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe,Finset.mem_biUnion] using hNew
end Oberwolfach
