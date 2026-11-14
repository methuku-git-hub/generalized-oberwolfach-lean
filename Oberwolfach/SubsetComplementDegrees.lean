module

public import Oberwolfach.TriangleTransformerFactors

@[expose] public section
/-! A graph and its complement partition the neighbours of a vertex in a
fixed set, apart from the vertex itself. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem subset_complement_degrees {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (S:Finset V) (v:V) (hv:v∈S):
    (G.neighborFinset v∩S).card+((Gᶜ).neighborFinset v∩S).card+1=S.card:=by
  have hpart:=Finset.card_filter_add_card_filter_not (s:=S) (fun w=>G.Adj v w)
  have heq:S.filter (fun w=>¬G.Adj v w)=((Gᶜ).neighborFinset v∩S)∪{v}:=by
    ext w
    simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_inter,Finset.mem_singleton,
      SimpleGraph.mem_neighborFinset,SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hw,hn⟩
      by_cases h:w=v
      · exact Or.inr h
      · exact Or.inl ⟨⟨Ne.symm h,hn⟩,hw⟩
    · rintro (⟨⟨hne,hn⟩,hw⟩|rfl)
      · exact ⟨hw,hn⟩
      · exact ⟨hv,by simp⟩
  have hd:Disjoint ((Gᶜ).neighborFinset v∩S) {v}:=by
    apply Finset.disjoint_singleton_right.mpr
    simp
  have heq2:S.filter (fun w=>G.Adj v w)=G.neighborFinset v∩S:=by ext w;simp [and_comm]
  rw [heq,heq2,Finset.card_union_of_disjoint hd,Finset.card_singleton] at hpart
  omega
theorem subset_explicit_complement_degrees {V:Type} [Fintype V] [DecidableEq V]
    (G P:SimpleGraph V) (hP:P=Gᶜ) (S:Finset V) (v:V) (hv:v∈S):
    (G.neighborFinset v∩S).card+(P.neighborFinset v∩S).card+1=S.card:=by
  have hp:(P.neighborFinset v∩S)=((Gᶜ).neighborFinset v∩S):=by
    ext w
    simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    rw [hP]
  rw [hp]
  exact subset_complement_degrees G S v hv
end Oberwolfach
