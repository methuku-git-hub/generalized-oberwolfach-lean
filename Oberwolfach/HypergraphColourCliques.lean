module

public import Oberwolfach.HypergraphCrossNeighbours
public import Oberwolfach.DisjointCliqueRestrictions
public import Oberwolfach.EqualizedColourRetention

@[expose] public section

/-! Resource cliques restricted to edges whose lists contain a given
colour. Rank and codegree bounds imply each required neighbourhood bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def hypergraphColourClique {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (z : V) (c : C) : Finset E :=
  Finset.univ.filter (fun e=>z∈R e ∧ c∈L e)

theorem hypergraphColourClique_isClique {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (z : V) (c : C) :
    ∀ e∈hypergraphColourClique R L z c,∀ f∈hypergraphColourClique R L z c,
      e≠f → (hypergraphLineGraph R).Adj e f := by
  intro e he f hf hne
  refine ⟨hne,?_⟩
  intro hd
  exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp he).2.1 (Finset.mem_filter.mp hf).2.1

theorem hypergraphColourClique_intersection
    {V E C : Type*} [Fintype E] (R : E → Finset V) (L : E → Finset C)
    {B : ℕ} (hcodeg : ∀ v w,v≠w →
      (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (z w : V) (hzw : z≠w) (c : C) :
    (hypergraphColourClique R L z c∩hypergraphColourClique R L w c).card≤B := by
  classical
  apply (Finset.card_le_card (show
    hypergraphColourClique R L z c∩hypergraphColourClique R L w c⊆
      Finset.univ.filter (fun e=>z∈R e ∧ w∈R e) from ?_)).trans (hcodeg z w hzw)
  intro e he
  obtain ⟨hz,hw⟩ := Finset.mem_inter.mp he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp hz).2.1,(Finset.mem_filter.mp hw).2.1⟩

theorem hypergraph_colour_neighbour_degree
    {V E C : Type*} [Fintype E] (R : E → Finset V) (L : E → Finset C)
    {k s : ℕ} (hsize : ∀ e,(R e).card≤k)
    (c : C) (hdegree : ∀ v,(hypergraphColourClique R L v c).card≤s) (e : E) :
    (colourNeighbourSet (hypergraphLineGraph R) L e c).card≤k*s := by
  classical
  have hsub : colourNeighbourSet (hypergraphLineGraph R) L e c⊆
      (R e).biUnion (fun v=>hypergraphColourClique R L v c) := by
    intro f hf
    obtain ⟨_,⟨_,hdis⟩,hc⟩ := Finset.mem_filter.mp hf
    obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hdis
    exact Finset.mem_biUnion.mpr ⟨v,hve,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvf,hc⟩⟩
  calc
    _ ≤ ((R e).biUnion (fun v=>hypergraphColourClique R L v c)).card := Finset.card_le_card hsub
    _ ≤ (R e).card*s := Finset.card_biUnion_le_card_mul _ _ _ (fun v _=>hdegree v)
    _ ≤ _ := Nat.mul_le_mul_right _ (hsize e)

theorem hypergraph_colour_common_neighbours
    {V E C : Type*} [Fintype E] (R : E → Finset V) (L : E → Finset C)
    {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (c : C) (e f : E) (hef : e≠f) (hn : ¬(hypergraphLineGraph R).Adj e f) :
    (colourNeighbourSet (hypergraphLineGraph R) L e c∩
      colourNeighbourSet (hypergraphLineGraph R) L f c).card≤k^2*B := by
  classical
  have hdis : Disjoint (R e) (R f) := by
    by_contra h
    exact hn ⟨hef,h⟩
  apply (Finset.card_le_card (show
    colourNeighbourSet (hypergraphLineGraph R) L e c∩
        colourNeighbourSet (hypergraphLineGraph R) L f c⊆
      Finset.univ.filter (fun g=>(hypergraphLineGraph R).Adj e g ∧
        (hypergraphLineGraph R).Adj f g) from ?_)).trans
      (hypergraphLineGraph_common_neighbours R hsize hcodeg e f hdis)
  intro g hg
  obtain ⟨he,hf⟩ := Finset.mem_inter.mp hg
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp he).2.1,(Finset.mem_filter.mp hf).2.1⟩

theorem restricted_hypergraph_clique_cross_degree
    {V E C J : Type*} [Fintype E] [Fintype J]
    (R : E → Finset V) (L : E → Finset C) (z : J → V)
    {k B : ℕ} (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (c : C) (i j : J) (hij : i≠j) (e : E)
    (he : e∈disjointFamilyRestriction Finset.univ (fun j=>hypergraphColourClique R L (z j) c) i) :
    ((disjointFamilyRestriction Finset.univ (fun j=>hypergraphColourClique R L (z j) c) j).filter
      ((hypergraphLineGraph R).Adj e)).card≤k*B := by
  classical
  let T := fun j=>hypergraphColourClique R L (z j) c
  let T' := disjointFamilyRestriction Finset.univ T
  have he' : e∈T i ∧ ∀ j∈(Finset.univ : Finset J),j≠i → e∉T j := by
    simpa only [disjointFamilyRestriction,Finset.mem_filter] using he
  have heT : e∈T i := he'.1
  have hce : c∈L e := (Finset.mem_filter.mp heT).2.2
  have hn : z j∉R e := by
    intro hz
    exact he'.2 j (Finset.mem_univ _) (Ne.symm hij)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,hce⟩)
  exact hypergraph_neighbours_in_other_clique R hsize hcodeg e (z j) hn (T' j)
    (fun f hf=>(Finset.mem_filter.mp
      (disjointFamilyRestriction_subset Finset.univ T j hf)).2.1)

end Oberwolfach
