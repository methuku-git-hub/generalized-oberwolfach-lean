module

public import Oberwolfach.HypergraphColourPadding
public import Oberwolfach.PartialListColouring
public import Oberwolfach.ColourRoundTests

@[expose] public section

/-! Removing the auxiliary padding after a colouring round. All tests use
the full padded experiment; only the retained edges and lists are restricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def originalColour {C D : Type*} : C ⊕ D → Option C
  | .inl c => some c
  | .inr _ => none

def paddedRetainedOriginal {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) : Option C :=
  (coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ (Sum.inl e)).bind originalColour

def paddedAvailableOriginal {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) : Finset C :=
  (L e).filter (fun c=>∀ v∈R e,∀ f∈hypergraphVertexClique (paddedResources R L s) v,
    coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ f≠some (Sum.inl c))

theorem paddedRetainedOriginal_eq_some
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) (c : C) : paddedRetainedOriginal R L s l σ e=some c ↔
      coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ (Sum.inl e)=some (Sum.inl c) := by
  unfold paddedRetainedOriginal
  cases h : coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ (Sum.inl e) with
  | none => simp
  | some b => cases b <;> simp [originalColour]

theorem paddedRetainedOriginal_list
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (hσ : ∀ e,(σ (Sum.inl e)).1∈paddedColourList R L s l (Sum.inl e))
    (e : E) (c : C) (hc : paddedRetainedOriginal R L s l σ e=some c) : c∈L e := by
  have hkeep := (paddedRetainedOriginal_eq_some R L s l σ e c).mp hc
  have he := (coinRetainedColour_eq_some _ _ _ _).mp hkeep |>.1
  have hm := hσ e
  rw [he] at hm
  exact (paddedColourList_original R L s l (Sum.inl e) c).mp hm

theorem paddedRetainedOriginal_proper
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e f : E) (hef : (hypergraphLineGraph R).Adj e f) (c : C)
    (hc : paddedRetainedOriginal R L s l σ e=some c) :
    paddedRetainedOriginal R L s l σ f≠some c := by
  intro hf
  exact coinRetainedColour_proper _ _
    ((paddedLineGraph_original_adj R L s e f).mpr hef) (Sum.inl c)
    ((paddedRetainedOriginal_eq_some R L s l σ e c).mp hc)
    ((paddedRetainedOriginal_eq_some R L s l σ f c).mp hf)

theorem paddedRetainedOriginal_none
    {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (hσ : ∀ e,(σ (Sum.inl e)).1∈paddedColourList R L s l (Sum.inl e))
    (e : E) : paddedRetainedOriginal R L s l σ e=none ↔
      ¬coinColourSurvives (hypergraphLineGraph (paddedResources R L s)) σ (Sum.inl e) := by
  have hm := hσ e
  obtain ⟨c,hc,he⟩ := Finset.mem_map.mp hm
  dsimp [Function.Embedding.inl] at he
  unfold paddedRetainedOriginal coinRetainedColour
  rw [← he]
  by_cases hs : coinColourSurvives (hypergraphLineGraph (paddedResources R L s)) σ (Sum.inl e)
  · simp [hs,originalColour]
  · simp [hs]

theorem paddedAvailableOriginal_map
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) :
    (paddedAvailableOriginal R L s l σ e).map Function.Embedding.inl=
      nibbleAvailableColours (hypergraphLineGraph (paddedResources R L s)) (R e)
        (hypergraphVertexClique (paddedResources R L s)) (paddedColourList R L s l (Sum.inl e)) σ := by
  classical
  ext b
  cases b with
  | inl c => simp [paddedAvailableOriginal,nibbleAvailableColours,paddedColourList]
  | inr d => simp [paddedAvailableOriginal,nibbleAvailableColours,paddedColourList]

theorem paddedAvailableOriginal_card
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) :
    (paddedAvailableOriginal R L s l σ e).card=
      (nibbleAvailableColours (hypergraphLineGraph (paddedResources R L s)) (R e)
        (hypergraphVertexClique (paddedResources R L s)) (paddedColourList R L s l (Sum.inl e)) σ).card := by
  rw [← paddedAvailableOriginal_map,Finset.card_map]

theorem paddedAvailableOriginal_subset
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e : E) : paddedAvailableOriginal R L s l σ e⊆L e := Finset.filter_subset _ _

theorem paddedAvailableOriginal_avoids_retained
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (e f : E) (hef : (hypergraphLineGraph R).Adj e f)
    (c : C) (hc : c∈paddedAvailableOriginal R L s l σ e) :
    paddedRetainedOriginal R L s l σ f≠some c := by
  intro hkeep
  have ha : ∀ v∈R e,∀ g∈hypergraphVertexClique (paddedResources R L s) v,
      coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ g≠some (Sum.inl c) :=
    (Finset.mem_filter.mp hc).2
  obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hef.2
  exact ha v hve (Sum.inl f) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvf⟩)
    ((paddedRetainedOriginal_eq_some R L s l σ f c).mp hkeep)

theorem padded_residual_colour_degree_bound
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (s l : ℕ)
    (σ : (E ⊕ ColourPaddingVertex R L s) → PaddedColour R L s l × Bool)
    (hσ : ∀ e,(σ (Sum.inl e)).1∈paddedColourList R L s l (Sum.inl e))
    (z : V) (c : C) :
    (hypergraphColourClique
      (fun e : {e // paddedRetainedOriginal R L s l σ e=none}=>R e.val)
      (fun e=>paddedAvailableOriginal R L s l σ e.val) z c).card≤
      (remainingColourVertices (hypergraphLineGraph (paddedResources R L s))
        (realColourClass (paddedResources R L s) (paddedColourList R L s l)
          (Finset.univ.map Function.Embedding.inl) z (Sum.inl c))
        (fun e=>(paddedResources R L s e).erase z)
        (hypergraphVertexClique (paddedResources R L s)) (Sum.inl c) σ).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (f:=fun e : {e // paddedRetainedOriginal R L s l σ e=none}=>Sum.inl e.val)
  · intro e he
    have hm : z∈R e.val ∧ c∈paddedAvailableOriginal R L s l σ e.val := by
      simpa only [Finset.mem_coe,hypergraphColourClique,Finset.mem_filter,Finset.mem_univ,true_and] using he
    have ha : c∈L e.val ∧ ∀ v∈R e.val,∀ f∈hypergraphVertexClique (paddedResources R L s) v,
        coinRetainedColour (hypergraphLineGraph (paddedResources R L s)) σ f≠some (Sum.inl c) := by
      simpa only [paddedAvailableOriginal,Finset.mem_filter] using hm.2
    simp only [Finset.mem_coe,remainingColourVertices,Finset.mem_filter]
    refine ⟨?_,(paddedRetainedOriginal_none R L s l σ hσ e.val).mp e.property,?_⟩
    · simp only [realColourClass,Finset.mem_filter]
      refine ⟨Finset.mem_map.mpr ⟨e.val,Finset.mem_univ _,rfl⟩,hm.1,?_⟩
      exact (paddedColourList_original R L s l (Sum.inl e.val) c).mpr ha.1
    · intro v hv f hf
      exact ha.2 v (Finset.mem_of_mem_erase hv) f hf
  · intro e _ f _ hef
    exact Subtype.ext (Sum.inl.inj hef)

end Oberwolfach
