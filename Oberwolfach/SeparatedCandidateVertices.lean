module

public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Choose actual vertices from specified candidate sets. The exclusion
cost is the size of the forbidden set plus the vertices and conflict
neighbours of the prescribed roots; no probability factor is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem candidate_vertex_avoiding (F:SimpleGraph V) (C W R:Finset V)
    (d c:ℝ) (hF:∀ v,(F.degree v:ℝ)≤d) (hC:c≤(C.card:ℝ))
    (hbudget:W.card+(R.card:ℝ)*(d+1)<c):
    ∃ v∈C,v∉W∧v∉R∧∀ w∈R,¬F.Adj v w:=by
  let D:=W∪(R∪R.biUnion (fun v=>F.neighborFinset v))
  have hR:=forbidden_used_neighbours_card F R d hF
  have hu:(D.card:ℝ)≤W.card+(R∪R.biUnion (fun v=>F.neighborFinset v)).card:=by
    exact_mod_cast Finset.card_union_le W (R∪R.biUnion (fun v=>F.neighborFinset v))
  have hlt:D.card<C.card:=by exact_mod_cast (show (D.card:ℝ)<C.card by linarith only [hR,hu,hC,hbudget])
  obtain ⟨v,hv,hvD⟩:=Finset.exists_mem_notMem_of_card_lt_card hlt
  have hout:v∉W∧v∉R∧v∉R.biUnion (fun v=>F.neighborFinset v):=by
    simpa only [D,Finset.mem_union,not_or] using hvD
  refine ⟨v,hv,hout.1,hout.2.1,?_⟩
  intro w hw hadj
  exact hout.2.2 (Finset.mem_biUnion.mpr ⟨w,hw,(F.mem_neighborFinset w v).mpr hadj.symm⟩)

theorem separated_candidate_vertices (F:SimpleGraph V) (C:I→Finset V) (W R:Finset V)
    (d c:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d) (hC:∀ i,c≤((C i).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+Fintype.card I)*(d+1)<c):
    ∃ p:I↪V,(∀ i,p i∈C i∧p i∉W∧p i∉R∧∀ v∈R,¬F.Adj (p i) v)∧
      ∀ i j,¬F.Adj (p i) (p j):=by
  let Good:I→V→Prop:=fun i v=>v∈C i∧v∉R∧∀ w∈R,¬F.Adj v w
  have hc:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*1*(d+1)→
      ∃ v,Good i v∧({v}:Finset V).card≤1∧Disjoint ({v}:Finset V) B:=by
    intro i B hB
    obtain ⟨v,hv,hvB,hvR,hvF⟩:=candidate_vertex_avoiding F (C i) B R d c hF (hC i)
      (by linarith only [hB,hbudget])
    exact ⟨v,⟨hv,hvR,hvF⟩,by simp,by simpa using hvB⟩
  obtain ⟨p,hp,hsep⟩:=finite_conflict_separated_choices (fun v:V=>({v}:Finset V)) Good W 1 F d hd hF (by simpa only [Nat.cast_one] using hc)
  have hinj:Function.Injective p:=by
    intro i j he
    by_contra hij
    have hh:=(hsep i j hij).1
    simpa only [he,Finset.disjoint_singleton_left,Finset.mem_singleton,not_true_eq_false] using hh
  refine ⟨⟨p,hinj⟩,?_,?_⟩
  · intro i
    exact ⟨(hp i).1.1,by simpa using (hp i).2.2,(hp i).1.2.1,(hp i).1.2.2⟩
  · intro i j
    by_cases he:i=j
    · subst j;exact F.loopless.irrefl _
    · exact (hsep i j he).2 _ (by simp) _ (by simp)

end Oberwolfach
