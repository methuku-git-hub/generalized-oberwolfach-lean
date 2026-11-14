module

public import Oberwolfach.EdgeAssignmentGraph
public import Oberwolfach.EdgeAssignmentOptionToFunction

@[expose] public section
/-! The original prescribed-edge assignment, stated as an actual function
on the graph's edge set, including the empty graph case. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem graph_edge_assignment_original (G:SimpleGraph V) (L:Sym2 V→Finset W) (B:V→Finset W)
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<Fintype.card V)
    (hL:∀e∈G.edgeFinset,a*Fintype.card V≤((L e).card:ℝ))
    (hB:∀v,((B v).card:ℝ)≤b*Fintype.card V)
    (hG:∀v,(G.degree v:ℝ)≤b*Fintype.card V):
    let K:=⌈4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊;
    ∃f:{e:Sym2 V // e∈G.edgeFinset}→W,
      (∀e,f e∈L e.1 ∧ ∀v∈e.1.toFinset,f e∉B v) ∧
      (∀e e',e≠e'→¬Disjoint e.1.toFinset e'.1.toFinset→f e≠f e') ∧
      (∀w,(Finset.univ.filter (fun e:{e:Sym2 V // e∈G.edgeFinset}=>f e=w)).card≤K) := by
  intro K
  obtain ⟨h,hallowed,hconf,hcap⟩:=graph_edge_assignment G L B a b ha hb hbsmall hn hL hB hG
  have hfull:∀e∈G.edgeFinset,∃w,h e=some w:=by
    intro e he
    obtain ⟨w,hw,_,_⟩:=hallowed e he
    exact ⟨w,hw⟩
  obtain ⟨f,hf,hcard⟩:=edge_assignment_option_to_function G.edgeFinset h hfull
  refine ⟨f,?_,?_,?_⟩
  · intro e
    obtain ⟨w,hw,hLw,hBw⟩:=hallowed e.1 e.2
    have heq:f e=w:=Option.some.inj ((hf e).symm.trans hw)
    simpa [heq] using And.intro hLw hBw
  · intro e e' hne hc heq
    have hvne:e.1≠e'.1:=by intro h;exact hne (Subtype.ext h)
    have hh:=hconf e.1 e.2 e'.1 e'.2 hvne hc
    apply hh
    rw [hf e,hf e',heq]
  · intro w
    rw [hcard w]
    exact hcap w
end Oberwolfach
