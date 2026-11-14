module

public import Oberwolfach.EdgeAssignmentOptionToFunction
public import Oberwolfach.EdgeConflictDegree

@[expose] public section
/-! Extend an edge-subtype assignment arbitrarily outside the graph. The
assignment on graph edges and the per-index capacity are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty W]

def extendEdgeAssignment (G:SimpleGraph V) (f:{e:Sym2 V // e∈G.edgeFinset}→W):Sym2 V→W:=
  fun e=>if he:e∈G.edgeFinset then f ⟨e,he⟩ else Classical.choice inferInstance

theorem extend_edge_assignment_value (G:SimpleGraph V) (f:{e:Sym2 V // e∈G.edgeFinset}→W)
    (e:Sym2 V) (he:e∈G.edgeFinset):extendEdgeAssignment G f e=f ⟨e,he⟩:=by
  simp [extendEdgeAssignment,he]

theorem extend_edge_assignment_fiber_card (G:SimpleGraph V) (f:{e:Sym2 V // e∈G.edgeFinset}→W) (w:W):
    (G.edgeFinset.filter (fun e=>extendEdgeAssignment G f e=w)).card=
      (Finset.univ.filter (fun e:{e:Sym2 V // e∈G.edgeFinset}=>f e=w)).card := by
  symm
  apply Finset.card_bij (fun e _=>e.1)
  · intro e he
    have he':f e=w:=(Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨e.2,by simpa [extend_edge_assignment_value G f e.1 e.2] using he'⟩
  · intro a ha b hb hab;exact Subtype.ext hab
  · intro e he
    have hh:=Finset.mem_filter.mp he
    let x:{e:Sym2 V // e∈G.edgeFinset}:=⟨e,hh.1⟩
    have hx:f x=w:=by simpa [extend_edge_assignment_value G f e hh.1] using hh.2
    exact ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩,rfl⟩

theorem extend_edge_assignment_matching (G:SimpleGraph V) (f:{e:Sym2 V // e∈G.edgeFinset}→W)
    (hmatch:∀e e',e≠e'→edgeAssignmentConflict e.1 e'.1→f e≠f e'):
    ∀i,∀e∈G.edgeFinset,∀e'∈G.edgeFinset,
      extendEdgeAssignment G f e=i→extendEdgeAssignment G f e'=i→e≠e'→Disjoint e.toFinset e'.toFinset := by
  intro i e he e' he' hi hi' hne
  by_contra hdis
  let x:{e:Sym2 V // e∈G.edgeFinset}:=⟨e,he⟩
  let y:{e:Sym2 V // e∈G.edgeFinset}:=⟨e',he'⟩
  have hxy:x≠y:=by intro h;exact hne (congrArg Subtype.val h)
  have hc:edgeAssignmentConflict x.1 y.1:=hdis
  have hf:f x=f y:=by
    have h1:f x=i:=by simpa [x,extend_edge_assignment_value G f e he] using hi
    have h2:f y=i:=by simpa [y,extend_edge_assignment_value G f e' he'] using hi'
    exact h1.trans h2.symm
  exact hmatch x y hxy hc hf
end Oberwolfach
