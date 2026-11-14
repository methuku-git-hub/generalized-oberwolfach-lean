module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! Pairwise overlap and membership bounds for boundary supports follow from
the physical graph's common-neighborhood and degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W I:Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

theorem boundary_support_bounds_of_physical_graph (G:SimpleGraph W) (e:I↪W) (S:I→Finset W)
    (hS:∀i,S i⊆G.neighborFinset (e i)):
    (∀i j,((S i∩S j).card:ℝ)≤((G.neighborFinset (e i)∩G.neighborFinset (e j)).card:ℝ)) ∧
    (∀w,((Finset.univ.filter (fun i=>w∈S i)).card:ℝ)≤(G.degree w:ℝ)):=by
  refine ⟨?_,?_⟩
  · intro i j
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter (hS i) (hS j))
  · intro w
    let A:=Finset.univ.filter (fun i=>w∈S i)
    have hsub:A.image e⊆G.neighborFinset w:=by
      intro v hv
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hv
      have hw:(G.Adj (e i) w):=(G.mem_neighborFinset (e i) w).mp (hS i ((Finset.mem_filter.mp hi).2))
      exact (G.mem_neighborFinset w (e i)).mpr hw.symm
    have hcard:A.card≤G.degree w:=by
      calc
        A.card=(A.image e).card:=(Finset.card_image_of_injective A e.injective).symm
        _≤(G.neighborFinset w).card:=Finset.card_le_card hsub
        _=G.degree w:=SimpleGraph.card_neighborFinset_eq_degree G w
    exact_mod_cast hcard
end Oberwolfach
