module

public import Oberwolfach.GraphEdgeAssignmentOriginal
public import Oberwolfach.AssignedEdgesCallerInputs
public import Oberwolfach.AssignedEdgeOrientation
public import Oberwolfach.PrescribedAssignedArcMatching
public import Oberwolfach.PrescribedAssignedArcCard

@[expose] public section
/-! Construct the actual matching assignment and orientation used by the
prescribed-family embedding, with the same bad-edge graph and lists. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] [Nonempty V] [Nonempty W]

theorem prepare_assigned_bad_edges (G:SimpleGraph V) (Dstar:V→V→Prop)
    (hDstar:∀x y,G.Adj x y→Dstar x y ∨ Dstar y x)
    (L:Sym2 V→Finset W) (B:V→Finset W) (old:W→Finset V) (inner:Finset W)
    (hOld:∀v i,v∈old i→i∈B v) (hOutside:∀e∈G.edgeFinset,Disjoint (L e) inner)
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<Fintype.card V)
    (hL:∀e∈G.edgeFinset,a*Fintype.card V≤((L e).card:ℝ))
    (hB:∀v,((B v).card:ℝ)≤b*Fintype.card V)
    (hG:∀v,(G.degree v:ℝ)≤b*Fintype.card V):
    let K:=⌈4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊;
    ∃ (assign:Sym2 V→W) (orient:Sym2 V→V×V),
      (∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈G.edgeFinset,assign e∈L e ∧ ∀v∈e.toFinset,assign e∉B v) ∧
      (∀i,∀e∈G.edgeFinset,∀e'∈G.edgeFinset,assign e=i→assign e'=i→e≠e'→Disjoint e.toFinset e'.toFinset) ∧
      (∀i,(G.edgeFinset.filter (fun e=>assign e=i)).card≤K) ∧
      (∀i,Disjoint (old i) (prescribedMatchingEndpoints (prescribedAssignedArcs G assign orient i))) ∧
      (∀i,i∈inner→prescribedAssignedArcs G assign orient i=∅) ∧
      (∀i,IsPrescribedOrientedMatching (prescribedAssignedArcs G assign orient i)) ∧
      (∀i,(prescribedAssignedArcs G assign orient i).card≤K) := by
  intro K
  obtain ⟨f,hallowed,hmatching,hcap⟩:=graph_edge_assignment_original G L B a b ha hb hbsmall hn hL hB hG
  obtain ⟨orient,horient⟩:=assigned_edge_orientation G Dstar hDstar
  let assign:=extendEdgeAssignment G f
  have ha':∀e∈G.edgeFinset,assign e∈L e ∧ ∀v∈e.toFinset,assign e∉B v:=by
    intro e he
    simpa [assign,extend_edge_assignment_value G f e he] using hallowed ⟨e,he⟩
  have hm:=extend_edge_assignment_matching G f (by
    intro e e' hne hc
    exact hmatching e e' hne hc)
  have hc:∀i,(G.edgeFinset.filter (fun e=>assign e=i)).card≤K:=by
    intro i
    rw [show assign=extendEdgeAssignment G f from rfl,extend_edge_assignment_fiber_card]
    exact hcap i
  have hphys:∀e∈G.edgeFinset,prescribedArcPhysical (orient e)=e:=fun e he=>(horient e he).1
  have hold:=assigned_edges_avoid_old_images G f orient hphys B old hOld (fun e=>(hallowed e).2)
  have hinner:=assigned_edges_avoid_inner_indices G f orient L inner (fun e=>(hallowed e).1) hOutside
  have hM:=prescribed_assigned_arcs_are_matchings G assign orient hphys hm
  have hcard:∀i,(prescribedAssignedArcs G assign orient i).card≤K:=by
    intro i
    rw [prescribed_assigned_arc_card G assign orient hphys]
    exact hc i
  exact ⟨assign,orient,horient,ha',hm,hc,hold,hinner,hM,hcard⟩
end Oberwolfach
