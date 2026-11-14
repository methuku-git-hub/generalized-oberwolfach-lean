module

public import Oberwolfach.LongInnerUnembeddedUsedRepair
public import Oberwolfach.LongRequiredExtendedHost

@[expose] public section
/-! Only matching-allocated edges that actually belong to the current regular
class can be prescribed into that class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def longClassInnerRequiredRepair (S Used K:SimpleGraph V) (I:Finset V) (Pack:Finset (Sym2 V)):SimpleGraph V:=
  K⊔spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I

theorem long_class_inner_required_repair_properties
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hPack:Pack⊆Used.edgeFinset) (hUsedSel:∀x y,Used.Adj x y→¬Sel.Adj x y):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Extra:=spanningRestriction ((S⊓Used)\Old) I
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    Kplus≤S ∧ Disjoint Kplus.edgeFinset Pack ∧
    (∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→s(x,y)∉Pack→Kplus.Adj x y) ∧
    (∀x y,Extra.Adj x y→¬Sel.Adj x y) ∧
    (∀v,Kplus.degree v≤K.degree v+I.card) ∧
    ((Extra.edgeFinset.card:ℝ)≤(I.card:ℝ)^2):=by
  intro K Old Extra Kplus
  have hKpack:Disjoint K.edgeFinset Pack:=
    long_required_graph_avoids_used_packing S (S\Used) Sel Used π d I D Pack (by intro x y h;exact h) hPack
  have hKold:∀x y,K.Adj x y→¬Old.Adj x y:=by
    intro x y hk ho
    have hh:s(x,y)∈Pack ∧ x≠y:=by simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using ho
    exact Finset.disjoint_left.mp hKpack (SimpleGraph.mem_edgeFinset.mpr hk) hh.1
  have hKcover:∀x y,x∈I→y∈I→S.Adj x y→¬Sel.Adj x y→¬(S⊓Used).Adj x y→K.Adj x y:=by
    intro x y hx hy hs hn hu
    change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)).Adj x y
    simp only [SimpleGraph.sup_adj]
    exact Or.inl ((spanningRestriction_adj _ _ _ _).mpr ⟨⟨⟨hs,fun h=>hu ⟨hs,h⟩⟩,hn⟩,hx,hy⟩)
  have hSU:∀x y,(S⊓Used).Adj x y→¬Sel.Adj x y:=fun x y h=>hUsedSel x y h.2
  obtain ⟨havoid,hcover,hsel,hdeg,hcard⟩:=long_inner_unembedded_used_repair S Sel (S⊓Used) Old K I hKold hKcover hSU
  have hKsub:K≤S:=by
    intro x y h
    change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y)).Adj x y at h
    rcases h with h|h
    · exact ((spanningRestriction_adj _ _ _ _).mp h).1.1.1
    · exact h.1
  refine ⟨?_,?_,?_,hsel,?_,hcard⟩
  · intro x y h
    rcases h with hk|he
    · exact hKsub hk
    · exact ((spanningRestriction_adj _ _ _ _).mp he).1.1.1
  · apply Finset.disjoint_left.mpr
    intro e he hp
    induction e using Sym2.ind with
    | _ x y =>
      have hk:Kplus.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
      have ho:Old.Adj x y:=by simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using And.intro hp hk.ne
      exact havoid x y hk ho
  · intro x y hx hy hs hsel' hp
    apply hcover x y hx hy hs hsel'
    intro ho
    have hh:s(x,y)∈Pack ∧ x≠y:=by simpa only [Old,SimpleGraph.fromEdgeSet_adj,Finset.mem_coe] using ho
    exact hp hh.1
  · intro v
    convert hdeg v using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
end Oberwolfach
