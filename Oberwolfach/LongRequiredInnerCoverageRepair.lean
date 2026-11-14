module

public import Oberwolfach.LongInnerUnembeddedUsedRepair

@[expose] public section
/-! Instantiation of the inner repair for the first-vortex required graph.
The older packing may be any actual set of edges contained in Used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_required_inner_coverage_repair
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hPack:Pack⊆Used.edgeFinset) (hUsedSel:∀x y,Used.Adj x y→¬Sel.Adj x y):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Extra:=spanningRestriction (Used\Old) I
    let Kplus:=K⊔Extra
    let J:=spanningRestriction (S\Used) I\Kplus
    Disjoint Kplus.edgeFinset Pack ∧
    Disjoint Used.edgeFinset J.edgeFinset ∧
    (∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→s(x,y)∉Pack→Kplus.Adj x y) ∧
    (∀x y,Extra.Adj x y→¬Sel.Adj x y) ∧
    (∀v,Kplus.degree v≤K.degree v+I.card) ∧
    ((Extra.edgeFinset.card:ℝ)≤(I.card:ℝ)^2):=by
  intro K Old Extra Kplus J
  have hKpack:Disjoint K.edgeFinset Pack:=
    long_required_graph_avoids_used_packing S (S\Used) Sel Used π d I D Pack (by intro x y h;exact h) hPack
  have hKold:∀x y,K.Adj x y→¬Old.Adj x y:=by
    intro x y hk ho
    have hmem:s(x,y)∈Pack:=by
      have hh:s(x,y)∈Pack ∧ x≠y:=by simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using ho
      exact hh.1
    exact Finset.disjoint_left.mp hKpack (SimpleGraph.mem_edgeFinset.mpr hk) hmem
  have hKcover:∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→¬Used.Adj x y→K.Adj x y:=by
    intro x y hx hy hs hn hu
    change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)).Adj x y
    simp only [SimpleGraph.sup_adj]
    exact Or.inl ((spanningRestriction_adj _ _ _ _).mpr ⟨⟨⟨hs,hu⟩,hn⟩,hx,hy⟩)
  obtain ⟨havoid,hcover,hsel,hdeg,hcard⟩:=long_inner_unembedded_used_repair S Sel Used Old K I hKold hKcover hUsedSel
  refine ⟨?_,?_,?_,hsel,hdeg,hcard⟩
  · apply Finset.disjoint_left.mpr
    intro e he hp
    induction e using Sym2.ind with
    | _ x y =>
      have hk:Kplus.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
      have ho:Old.Adj x y:=by
        simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using And.intro hp hk.ne
      exact havoid x y hk ho
  · apply Finset.disjoint_left.mpr
    intro e he hj
    induction e using Sym2.ind with
    | _ x y =>
      have hu:Used.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
      have hJ:J.Adj x y:=SimpleGraph.mem_edgeFinset.mp hj
      have hnot:=((spanningRestriction_adj _ _ _ _).mp hJ.1).1.2
      exact hnot hu
  · intro x y hx hy hs hsel' hp
    apply hcover x y hx hy hs hsel'
    intro ho
    have hh:s(x,y)∈Pack ∧ x≠y:=by simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using ho
    exact hp hh.1
end Oberwolfach
