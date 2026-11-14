module

public import Oberwolfach.NeighbourhoodLocalLemma
public import Oberwolfach.RemainingColourDegrees

@[expose] public section

/-! The available lists and remaining colour degrees depend on fixed
coordinates within two graph steps. The supports do not depend on the
sampled colours or on later choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem coinRetainedColour_congr
    {V C : Type*} (G : SimpleGraph V) (σ τ : V → C×Bool) (v : V)
    (hv : σ v=τ v) (hN : ∀ u,G.Adj v u → σ u=τ u) :
    coinRetainedColour G σ v=coinRetainedColour G τ v := by
  unfold coinRetainedColour
  rw [coinColourSurvives_congr G σ τ v hv hN,hv]

theorem coinRetainedColour_congr_on_closed
    {V C : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (σ τ : V → C×Bool)
    (he : ∀ u∈closedSetNeighbours G S,σ u=τ u)
    (v : V) (hv : v∈S) : coinRetainedColour G σ v=coinRetainedColour G τ v := by
  apply coinRetainedColour_congr G σ τ v
  · exact he v ((closedSetNeighbours_mem_iff G S v).mpr ⟨v,hv,Or.inl rfl⟩)
  · intro u hu
    exact he u ((closedSetNeighbours_mem_iff G S u).mpr ⟨v,hv,Or.inr hu⟩)

theorem nibbleAvailableColours_support
    {V C J : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V) (L : Finset C)
    (σ τ : V → C×Bool)
    (he : ∀ u∈closedSetNeighbours G (Q.biUnion T),σ u=τ u) :
    nibbleAvailableColours G Q T L σ=nibbleAvailableColours G Q T L τ := by
  ext c
  simp only [nibbleAvailableColours,Finset.mem_filter]
  apply and_congr_right'
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [coinRetainedColour_congr_on_closed G (Q.biUnion T) σ τ he v
    (Finset.mem_biUnion.mpr ⟨j,hj,hv⟩)]

theorem remainingColourVertices_support
    {V C J : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (Q : V → Finset J) (T : J → Finset V)
    (c : C) (σ τ : V → C×Bool)
    (he : ∀ u∈closedSetNeighbours G (U∪U.biUnion (fun v=>(Q v).biUnion T)),σ u=τ u) :
    remainingColourVertices G U Q T c σ=remainingColourVertices G U Q T c τ := by
  classical
  let W := U∪U.biUnion (fun v=>(Q v).biUnion T)
  have hroot (v : V) (hv : v∈U) : coinColourSurvives G σ v ↔ coinColourSurvives G τ v := by
    apply coinColourSurvives_congr G σ τ v
    · exact he v ((closedSetNeighbours_mem_iff G W v).mpr ⟨v,Finset.mem_union_left _ hv,Or.inl rfl⟩)
    · intro u hu
      exact he u ((closedSetNeighbours_mem_iff G W u).mpr ⟨v,Finset.mem_union_left _ hv,Or.inr hu⟩)
  ext v
  simp only [remainingColourVertices,Finset.mem_filter]
  apply and_congr_right
  intro hv
  rw [hroot v hv]
  apply and_congr_right'
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  apply forall_congr'
  intro w
  apply forall_congr'
  intro hw
  have hm : w∈W := Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_biUnion.mpr ⟨j,hj,hw⟩⟩)
  rw [coinRetainedColour_congr_on_closed G W σ τ he w hm]

theorem hypergraph_resource_union_subset_neighbours
    {V E : Type*} [Fintype E] [DecidableEq E]
    (R : E → Finset V) (U : Finset E) (Q : E → Finset V)
    (hQ : ∀ e∈U,Q e⊆R e) :
    U∪U.biUnion (fun e=>(Q e).biUnion (hypergraphVertexClique R))⊆
      closedSetNeighbours (hypergraphLineGraph R) U := by
  classical
  intro f hf
  apply (closedSetNeighbours_mem_iff _ U f).mpr
  rcases Finset.mem_union.mp hf with hf|hf
  · exact ⟨f,hf,Or.inl rfl⟩
  · obtain ⟨e,he,hf⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨v,hv,hvf⟩ := Finset.mem_biUnion.mp hf
    have hve : v∈R e := hQ e he hv
    have hvf' : v∈R f := (Finset.mem_filter.mp hvf).2
    refine ⟨e,he,?_⟩
    by_cases hef : e=f
    · exact Or.inl hef
    · exact Or.inr ⟨hef,fun hd=>Finset.disjoint_left.mp hd hve hvf'⟩

theorem hypergraph_remainingColourVertices_support
    {V E C : Type*} [Fintype E] [DecidableEq E]
    (R : E → Finset V) (U : Finset E) (Q : E → Finset V)
    (hQ : ∀ e∈U,Q e⊆R e) (c : C) (σ τ : E → C×Bool)
    (he : ∀ u∈closedSetNeighbours (hypergraphLineGraph R)
      (closedSetNeighbours (hypergraphLineGraph R) U),σ u=τ u) :
    remainingColourVertices (hypergraphLineGraph R) U Q (hypergraphVertexClique R) c σ=
      remainingColourVertices (hypergraphLineGraph R) U Q (hypergraphVertexClique R) c τ := by
  apply remainingColourVertices_support
  intro u hu
  exact he u (closedSetNeighbours_mono _
    (hypergraph_resource_union_subset_neighbours R U Q hQ) hu)

theorem hypergraph_nibbleAvailableColours_support
    {V E C : Type*} [Fintype E] [DecidableEq E]
    (R : E → Finset V) (e : E) (L : Finset C) (σ τ : E → C×Bool)
    (he : ∀ u∈closedSetNeighbours (hypergraphLineGraph R)
      (closedSetNeighbours (hypergraphLineGraph R) {e}),σ u=τ u) :
    nibbleAvailableColours (hypergraphLineGraph R) (R e) (hypergraphVertexClique R) L σ=
      nibbleAvailableColours (hypergraphLineGraph R) (R e) (hypergraphVertexClique R) L τ := by
  apply nibbleAvailableColours_support
  intro u hu
  apply he u
  apply closedSetNeighbours_mono _ ?_ hu
  intro f hf
  exact hypergraph_resource_union_subset_neighbours R {e} R (fun _ _=>Finset.Subset.refl _)
    (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e,by simp,hf⟩))

end Oberwolfach
