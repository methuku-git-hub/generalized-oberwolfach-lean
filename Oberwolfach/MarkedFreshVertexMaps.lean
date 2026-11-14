module

public import Oberwolfach.MarkedHostGreedyChoices
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Choose actual new row and hub vertices for the finite expansion graphs.
Rows are mutually separated; no assumption is imposed on old-root pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_host_order_bounds
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch) (v₀:V):
    c≤(Fintype.card V:ℝ)∧ch≤(Fintype.card U:ℝ):=by
  constructor
  · exact (Q.outgoing false false v₀ ∅ (by simp)).trans (by exact_mod_cast Finset.card_le_univ _)
  · simpa using Q.hubs ∅ ∅ (by simp) (by simp) (by simp)

theorem marked_fresh_row_map (W Z:Finset V) (hc:c≤(Fintype.card V:ℝ))
    (hbudget:(W.card:ℝ)+(Fintype.card I+Z.card)*(2*b+1)<c):
    ∃ f:I↪V,(∀ i,f i∉W∧f i∉Z∧∀ z∈Z,¬PermutationClose π b (f i) z)∧
      PermutationSeparated π b f:=by
  let Good:I→V→Prop:=fun _ v=>v∉Z∧∀ z∈Z,¬PermutationClose π b v z
  have hchoose:∀ i:I,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*1*((2*b:ℝ)+1)→
      ∃ v,Good i v∧({v}:Finset V).card≤1∧Disjoint ({v}:Finset V) B:=by
    intro i B hB
    have hb:(B.card:ℝ)+Z.card*(2*b+1)<c:=by nlinarith only [hB,hbudget]
    obtain ⟨v,_,hav⟩:=marked_candidate_avoiding (π:=π) (b:=b) Finset.univ B Z (by simpa using hc) hb
    exact ⟨v,hav.2,by simp,by simpa using hav.1⟩
  obtain ⟨f,hf,hd⟩:=finite_conflict_separated_choices (fun v:V=>{v}) Good W 1
    (permutationConflictGraph π b) (2*b) (by positivity)
    (fun v=>by exact_mod_cast permutationConflictGraph_degree_le π b v) (by simpa only [Nat.cast_one] using hchoose)
  have hfi:Function.Injective f:=by
    intro i j he;by_contra hij
    exact Finset.disjoint_left.mp (hd i j hij).1 (Finset.mem_singleton_self _) (by simp [he])
  refine ⟨⟨f,hfi⟩,?_,?_⟩
  · intro i;exact ⟨by simpa using (hf i).2.2,(hf i).1⟩
  · intro i j hij hh
    exact (hd i j hij).2 _ (Finset.mem_singleton_self _) _ (Finset.mem_singleton_self _) ⟨fun he=>hij (hfi he),hh⟩

theorem finite_fresh_hub_map (B:Finset U)
    (hbudget:B.card+Fintype.card J≤Fintype.card U):
    ∃ g:J↪U,∀ j,g j∉B:=by
  let T:Finset U:=Finset.univ\B
  have ht:Fintype.card J≤Fintype.card T:=by
    rw [Fintype.card_coe,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]
    omega
  obtain ⟨g⟩:=Function.Embedding.nonempty_of_card_le ht
  refine ⟨g.trans (Function.Embedding.subtype (fun u=>u∈T)),?_⟩
  intro j
  exact (Finset.mem_sdiff.mp (g j).property).2

end Oberwolfach
