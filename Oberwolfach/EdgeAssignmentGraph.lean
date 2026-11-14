module

public import Oberwolfach.EdgeAssignmentGreedy
public import Oberwolfach.EdgeAssignmentBudget
public import Oberwolfach.EdgeForbiddenEndpoints

@[expose] public section
/-! Assign the edges of a graph to indices using the original list, degree,
forbidden-set and capacity bounds. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem graph_edge_assignment (G:SimpleGraph V) (L:Sym2 V→Finset W) (B:V→Finset W)
    (a b:ℝ) (ha:0<a) (hb:0≤b) (hbsmall:b≤a/16) (hn:0<Fintype.card V)
    (hL:∀e∈G.edgeFinset,a*Fintype.card V≤((L e).card:ℝ))
    (hB:∀v,((B v).card:ℝ)≤b*Fintype.card V)
    (hG:∀v,(G.degree v:ℝ)≤b*Fintype.card V):
    let K:=⌈4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V)⌉₊;
    ∃f:Sym2 V→Option W,
      (∀e∈G.edgeFinset,∃w,f e=some w ∧ w∈L e ∧ ∀v∈e.toFinset,w∉B v) ∧
      (∀e∈G.edgeFinset,∀e'∈G.edgeFinset,e≠e'→edgeAssignmentConflict e e'→f e≠f e') ∧
      (∀w,(G.edgeFinset.filter (fun e=>f e=some w)).card≤K) := by
  intro K
  by_cases hE:G.edgeFinset.Nonempty
  · obtain ⟨e₀,he₀⟩:=hE
    have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    have hLpos:(0:ℝ)<(L e₀).card:=(mul_pos ha hnR).trans_le (hL e₀ he₀)
    have hLposN:0<(L e₀).card:=by exact_mod_cast hLpos
    obtain ⟨w₀,hw₀⟩:=Finset.card_pos.mp hLposN
    letI:Nonempty W:=⟨w₀⟩
    have hEpos:(0:ℝ)<G.edgeFinset.card:=by exact_mod_cast Finset.card_pos.mpr ⟨e₀,he₀⟩
    have han:0<a*Fintype.card V:=mul_pos ha hnR
    have hquot:0<4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V):=by positivity
    have hceil:4*(G.edgeFinset.card:ℝ)/(a*Fintype.card V)≤(K:ℝ):=Nat.le_ceil _
    have hK:0<K:=by exact_mod_cast hquot.trans_le hceil
    have hbudget:∀e∈G.edgeFinset,((edgeAssignmentForbidden B e).card:ℝ)+
        ((G.edgeFinset.filter (edgeAssignmentConflict e)).card:ℝ)+(G.edgeFinset.card:ℝ)/K<(L e).card:=by
      intro e he
      induction e using Sym2.ind with
      | _ x y =>
        have hbad:=edge_assignment_forbidden_at_most B (b*Fintype.card V) hB x y
        have hconf:=edge_assignment_conflicts_at_most G x y
        have hconf':((G.edgeFinset.filter (edgeAssignmentConflict s(x,y))).card:ℝ)≤2*b*Fintype.card V:=by
          linarith [hG x,hG y]
        exact edge_assignment_numeric_budget a b (Fintype.card V) G.edgeFinset.card K
          (edgeAssignmentForbidden B s(x,y)).card (G.edgeFinset.filter (edgeAssignmentConflict s(x,y))).card (L s(x,y)).card
          ha hnR hb hbsmall (by exact_mod_cast hK) hceil (by positivity) (by simpa only [mul_assoc] using hbad) hconf' (hL s(x,y) he)
    obtain ⟨g,hallowed,hconf,hcap⟩:=edge_assignment_greedy G.edgeFinset L (edgeAssignmentForbidden B) edgeAssignmentConflict
      edge_assignment_conflict_symmetric K hK hbudget
    refine ⟨fun e=>some (g e),?_,?_,?_⟩
    · intro e he
      refine ⟨g e,rfl,(hallowed e he).1,?_⟩
      intro v hv hvB
      have hh:g e∈edgeAssignmentForbidden B e:=by
        exact Finset.mem_biUnion.mpr ⟨v,hv,hvB⟩
      exact (hallowed e he).2 hh
    · intro e he e' he' hne hc heq
      exact hconf e he e' he' hne hc (Option.some.inj heq)
    · intro w
      simpa using hcap w
  · have hEmpty:G.edgeFinset=∅:=Finset.not_nonempty_iff_eq_empty.mp hE
    refine ⟨fun _=>none,?_,?_,?_⟩
    · simp [hEmpty]
    · simp [hEmpty]
    · simp [hEmpty]
end Oberwolfach
