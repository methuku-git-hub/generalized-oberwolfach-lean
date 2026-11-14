module

public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Degree accounting for a graph whose exterior neighbourhoods have
already been identified. No independent sampling of deleted edges is used. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W I:Type} [Fintype W] [Fintype I] [DecidableEq W] [DecidableEq I]

theorem boundary_graph_degree (G:SimpleGraph W) (Ω:Finset W)
    (x:I↪W) (A:I→Finset W)
    (hout:∀ z∉Ω,∀ v,G.Adj z v↔∃ i,x i=z ∧ v∈A i)
    (d k:ℕ) (hinner:∀ v,(spanningRestriction G Ω).degree v≤d)
    (hmem:∀ v,(Finset.univ.filter (fun i=>v∈A i)).card≤k)
    (v:W) (hv:v∈Ω):G.degree v≤d+k:=by
  have hsub:G.neighborFinset v⊆(spanningRestriction G Ω).neighborFinset v∪
      (Finset.univ.filter (fun i=>v∈A i)).image x:=by
    intro z hz
    have hz':G.Adj v z:=(G.mem_neighborFinset v z).mp hz
    by_cases hΩ:z∈Ω
    · exact Finset.mem_union_left _ (((spanningRestriction G Ω).mem_neighborFinset v z).mpr
        ((spanningRestriction_adj G Ω v z).mpr ⟨hz',hv,hΩ⟩))
    · obtain ⟨i,hi,ha⟩:=(hout z hΩ v).mp hz'.symm
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,by simp [ha],hi⟩)
  calc
    G.degree v= (G.neighborFinset v).card:=rfl
    _≤((spanningRestriction G Ω).neighborFinset v∪
        (Finset.univ.filter (fun i=>v∈A i)).image x).card:=Finset.card_le_card hsub
    _≤((spanningRestriction G Ω).neighborFinset v).card+
        ((Finset.univ.filter (fun i=>v∈A i)).image x).card:=Finset.card_union_le _ _
    _≤d+k:=Nat.add_le_add (hinner v) (Finset.card_image_le.trans (hmem v))

theorem boundary_graph_root_degree (G:SimpleGraph W) (Ω:Finset W)
    (x:I↪W) (A:I→Finset W) (hx:∀ i,x i∉Ω)
    (hout:∀ z∉Ω,∀ v,G.Adj z v↔∃ i,x i=z ∧ v∈A i)
    (i:I):G.degree (x i)=(A i).card:=by
  change (G.neighborFinset (x i)).card=(A i).card
  congr 1
  ext v
  rw [SimpleGraph.mem_neighborFinset,hout (x i) (hx i)]
  constructor
  · rintro ⟨j,hj,hv⟩
    exact x.injective hj ▸ hv
  · intro hv;exact ⟨i,rfl,hv⟩

end Oberwolfach
