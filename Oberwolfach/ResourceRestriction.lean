module

public import Oberwolfach.ResourceDecompositions
public import Oberwolfach.HypergraphWeightMoments
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-! Transport the actual surviving indexed resources along a vertex
embedding. The resource identifier and its supplied weight are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C]

abbrev RestrictedResource (R : C → Finset V) (e : W ↪ V) :=
  {C₀ : C // ∀ v∈R C₀,∃ w,e w=v}

def restrictedResourceSet (R : C → Finset V) (e : W ↪ V)
    (C₀ : RestrictedResource R e) : Finset W :=
  Finset.univ.filter (fun w => e w∈R C₀.val)

theorem restrictedResourceSet_mem (R : C → Finset V) (e : W ↪ V)
    (C₀ : RestrictedResource R e) (w : W) :
    w∈restrictedResourceSet R e C₀ ↔ e w∈R C₀.val := by
  simp [restrictedResourceSet]

theorem restrictedResourceSet_image (R : C → Finset V) (e : W ↪ V)
    (C₀ : RestrictedResource R e) : (restrictedResourceSet R e C₀).image e=R C₀.val := by
  ext v
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact (restrictedResourceSet_mem R e C₀ w).mp hw
  · intro hv
    obtain ⟨w,rfl⟩ := C₀.property v hv
    exact Finset.mem_image.mpr ⟨w,(restrictedResourceSet_mem R e C₀ w).mpr hv,rfl⟩

theorem restrictedResourceSet_card (R : C → Finset V) (e : W ↪ V)
    (C₀ : RestrictedResource R e) : (restrictedResourceSet R e C₀).card=(R C₀.val).card := by
  rw [← restrictedResourceSet_image R e C₀,Finset.card_image_of_injective _ e.injective]

theorem restricted_resource_multiplicity (R : C → Finset V) (e : W ↪ V)
    (J : ℕ) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (Y : Finset W) :
    Fintype.card {C₀ : RestrictedResource R e // restrictedResourceSet R e C₀=Y} ≤ J := by
  let A := {C₀ : RestrictedResource R e // restrictedResourceSet R e C₀=Y}
  let B := {C₀ : C // R C₀=Y.image e}
  let f (C₀ : A) : B := ⟨C₀.val.val,by
    rw [← restrictedResourceSet_image R e C₀.val,C₀.property]⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => z.val) he
  exact (Fintype.card_le_of_injective f hf).trans (hJ _)

theorem restricted_resource_degree (R : C → Finset V) (e : W ↪ V) (w : C → ℝ) (v : W) :
    hypergraphWeightedDegree (restrictedResourceSet R e) (fun C₀ => w C₀.val) v=
      hypergraphWeightedDegree R
        (fun C₀ => if ∀ x∈R C₀,∃ y,e y=x then w C₀ else 0) (e v) := by
  unfold hypergraphWeightedDegree
  simp only [restrictedResourceSet_mem]
  have he := Finset.sum_subtype (F:=inferInstance) (p:=fun C₀ => ∀ x∈R C₀,∃ y,e y=x)
    (Finset.univ.filter (fun C₀ => ∀ x∈R C₀,∃ y,e y=x)) (by intro x;simp)
    (fun C₀ => if e v∈R C₀ then w C₀ else 0)
  rw [← he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro C₀ _
  by_cases hp : ∀ x∈R C₀,∃ y,e y=x <;> by_cases hv : e v∈R C₀ <;> simp [hp,hv]

theorem restricted_resource_decomposition_lift (R : C → Finset V) (e : W ↪ V)
    (A : Finset W) (hA : HasResourceDecomposition (restrictedResourceSet R e) A) :
    HasResourceDecomposition R (A.image e) := by
  obtain ⟨M,hM,hU⟩ := hA
  refine ⟨M.image Subtype.val,?_,?_⟩
  · intro a ha b hb hab
    obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
    rw [← restrictedResourceSet_image R e a',← restrictedResourceSet_image R e b']
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hw
    have he' := e.injective he
    subst y
    exact Finset.disjoint_left.mp (hM a' ha' b' hb' (fun h => hab (congrArg Subtype.val h))) hx hy
  · rw [← hU]
    ext v
    constructor
    · intro hv
      obtain ⟨C₀,hC,hv⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hC
      rw [← restrictedResourceSet_image R e D] at hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨x,Finset.mem_biUnion.mpr ⟨D,hD,hx⟩,rfl⟩
    · intro hv
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨D,hD,hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨D.val,Finset.mem_image.mpr ⟨D,hD,rfl⟩,
        (restrictedResourceSet_mem R e D x).mp hx⟩

end Oberwolfach
