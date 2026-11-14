module

public import Oberwolfach.SeparatedCandidateVertices

@[expose] public section

/-! Sequential pairs with a genuine dependence of the second candidate
set on the first selected vertex. Both coordinates remain distinct and
separated from all earlier pairs and all prescribed roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem separated_candidate_pairs (F:SimpleGraph V) (C:I→Finset V) (C':I→V→Finset V)
    (W R:Finset V) (d c:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hC:∀ i,c≤((C i).card:ℝ)) (hC':∀ i,∀ v∈C i,c≤((C' i v).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+2*Fintype.card I+1)*(d+1)<c):
    ∃ a b:I→V,
      (∀ i,a i∈C i∧b i∈C' i (a i)∧a i≠b i∧¬F.Adj (a i) (b i))∧
      (∀ i,∀ v∈({a i,b i}:Finset V),v∉W∧v∉R∧∀ w∈R,¬F.Adj v w)∧
      (∀ i j,i≠j→Disjoint ({a i,b i}:Finset V) {a j,b j})∧
      ∀ i j,∀ v∈({a i,b i}:Finset V),∀ w∈({a j,b j}:Finset V),¬F.Adj v w:=by
  let Good:I→V×V→Prop:=fun i ab=>ab.1∈C i∧ab.2∈C' i ab.1∧ab.1≠ab.2∧¬F.Adj ab.1 ab.2∧
    ∀ v∈({ab.1,ab.2}:Finset V),v∉R∧∀ w∈R,¬F.Adj v w
  have hc:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*2*(d+1)→
      ∃ ab:V×V,Good i ab∧({ab.1,ab.2}:Finset V).card≤2∧Disjoint ({ab.1,ab.2}:Finset V) B:=by
    intro i B hB
    have hbudget0:(B.card:ℝ)+R.card*(d+1)<c:=by nlinarith only [hB,hbudget,hd]
    obtain ⟨a,ha,haB,haR,haF⟩:=candidate_vertex_avoiding F (C i) B R d c hF (hC i) hbudget0
    have hRi:((insert a R).card:ℝ)≤R.card+1:=by exact_mod_cast Finset.card_insert_le a R
    have hbudget1:(B.card:ℝ)+(insert a R).card*(d+1)<c:=by
      have hh:=mul_le_mul_of_nonneg_right hRi (show 0≤d+1 by linarith)
      nlinarith only [hB,hbudget,hh]
    obtain ⟨b,hb,hbB,hbR,hbF⟩:=candidate_vertex_avoiding F (C' i a) B (insert a R) d c hF (hC' i a ha) hbudget1
    have hba:b≠a:=fun he=>hbR (by simp [he])
    have hfb:¬F.Adj b a:=hbF a (by simp)
    refine ⟨(a,b),⟨ha,hb,hba.symm,fun he=>hfb he.symm,?_⟩,?_,?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨haR,haF⟩
      · have he:=Finset.mem_singleton.mp hv
        subst v
        exact ⟨fun he=>hbR (Finset.mem_insert_of_mem he),fun w hw=>hbF w (Finset.mem_insert_of_mem hw)⟩
    · simpa using Finset.card_insert_le a ({b}:Finset V)
    · apply Finset.disjoint_left.mpr
      intro v hv hvB
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact haB hvB
      · have he:v=b:=Finset.mem_singleton.mp hv
        exact hbB (he ▸ hvB)
  obtain ⟨ab,hab,hsep⟩:=finite_conflict_separated_choices (fun ab:V×V=>({ab.1,ab.2}:Finset V)) Good W 2 F d hd hF (by simpa only [Nat.cast_ofNat] using hc)
  refine ⟨fun i=>(ab i).1,fun i=>(ab i).2,?_,?_,fun i j hij=>(hsep i j hij).1,?_⟩
  · intro i
    exact ⟨(hab i).1.1,(hab i).1.2.1,(hab i).1.2.2.1,(hab i).1.2.2.2.1⟩
  · intro i v hv
    exact ⟨fun hw=>Finset.disjoint_left.mp (hab i).2.2 hv hw,((hab i).1.2.2.2.2 v hv).1,
      ((hab i).1.2.2.2.2 v hv).2⟩
  · intro i j v hv w hw
    by_cases hij:i=j
    · subst j
      have hno:¬F.Adj (ab i).1 (ab i).2:=(hab i).1.2.2.2.1
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
      · exact F.loopless.irrefl _
      · exact hno
      · exact fun he=>hno he.symm
      · exact F.loopless.irrefl _
    · exact (hsep i j hij).2 v hv w hw

end Oberwolfach
