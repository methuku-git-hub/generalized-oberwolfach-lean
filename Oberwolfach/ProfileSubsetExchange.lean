module

public import Oberwolfach.ProfileRootSampling
public import Oberwolfach.SubsetExchangeCount

@[expose] public section

/-! The change of the actual union of class samples under one exchange.
The statements also allow an injective map into a larger ambient set,
so vertices fixed before sampling need not belong to the populations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)]

theorem profileRootSet_sdiff_card_le {a : I → ℕ}
    (σ τ : ∀ i,FixedSubset (V i) (a i)) (i : I)
    (hagree : ∀ j,j≠i → σ j=τ j) :
    (profileRootSet τ\profileRootSet σ).card ≤ ((τ i).val\(σ i).val).card := by
  have hs : profileRootSet τ\profileRootSet σ ⊆
      ((τ i).val\(σ i).val).image (fun v => (⟨i,v⟩ : Σ j,V j)) := by
    rintro ⟨j,v⟩ hx
    have hx' := Finset.mem_sdiff.mp hx
    by_cases hji : j=i
    · subst j
      exact Finset.mem_image.mpr ⟨v,Finset.mem_sdiff.mpr
        ⟨(profileRootSet_mem τ i v).mp hx'.1,
          fun hv => hx'.2 ((profileRootSet_mem σ i v).mpr hv)⟩,rfl⟩
    · have he := hagree j hji
      exact False.elim (hx'.2 ((profileRootSet_mem σ j v).mpr
        (by rw [he];exact (profileRootSet_mem τ j v).mp hx'.1)))
  exact (Finset.card_le_card hs).trans Finset.card_image_le

theorem profileRootSet_exchange_sdiff {a : I → ℕ}
    (σ τ : ∀ i,FixedSubset (V i) (a i)) (i : I)
    (hagree : ∀ j,j≠i → σ j=τ j) (u v : V i)
    (he : τ i=fixedSubsetMap (Equiv.swap u v) (σ i)) :
    (profileRootSet τ\profileRootSet σ).card ≤ 1 ∧
      (profileRootSet σ\profileRootSet τ).card ≤ 1 := by
  have h₁ := profileRootSet_sdiff_card_le σ τ i hagree
  have h₂ := profileRootSet_sdiff_card_le τ σ i (fun j hj => (hagree j hj).symm)
  have hback : fixedSubsetMap (Equiv.swap u v) (τ i)=σ i := by
    rw [he]
    apply Subtype.ext
    ext x
    simp [fixedSubsetMap]
  constructor
  · exact h₁.trans (by rw [he];simpa only [fixedSubsetMap] using swap_subset_new_card_le_one (σ i).val u v)
  · exact h₂.trans (by rw [← hback];simpa only [fixedSubsetMap] using swap_subset_new_card_le_one (τ i).val u v)

theorem union_mapped_sdiff_card_le {W : Type*} [DecidableEq W]
    (e : (Σ i,V i) ↪ W) (Z : Finset W) (A D : Finset (Σ i,V i)) :
    ((Z∪D.map e)\(Z∪A.map e)).card ≤ (D\A).card := by
  have hs : (Z∪D.map e)\(Z∪A.map e) ⊆ (D\A).map e := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hn : x∉Z := fun h => hx'.2 (Finset.mem_union_left _ h)
    have hd := (Finset.mem_union.mp hx'.1).resolve_left hn
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hd
    exact Finset.mem_map.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hy,
      fun ha => hx'.2 (Finset.mem_union_right _ (Finset.mem_map.mpr ⟨y,ha,rfl⟩))⟩,rfl⟩
  simpa only [Finset.card_map] using Finset.card_le_card hs

theorem profileSample_exchange_card_bounds {W : Type*} [DecidableEq W]
    (e : (Σ i,V i) ↪ W) (Z : Finset W) {a : I → ℕ}
    (σ τ : ∀ i,FixedSubset (V i) (a i)) (i : I)
    (hagree : ∀ j,j≠i → σ j=τ j) (u v : V i)
    (he : τ i=fixedSubsetMap (Equiv.swap u v) (σ i)) :
    ((Z∪(profileRootSet σ).map e)\(Z∪(profileRootSet τ).map e)).card ≤ 1 ∧
    ((Z∪(profileRootSet τ).map e)\(Z∪(profileRootSet σ).map e)).card ≤ 1 ∧
    ((Z∪(profileRootSet σ).map e)∪(Z∪(profileRootSet τ).map e)).card ≤ Z.card+(∑ j,a j)+1 := by
  have hs := profileRootSet_exchange_sdiff σ τ i hagree u v he
  have h₁ := (union_mapped_sdiff_card_le e Z (profileRootSet τ) (profileRootSet σ)).trans hs.2
  have h₂ := (union_mapped_sdiff_card_le e Z (profileRootSet σ) (profileRootSet τ)).trans hs.1
  refine ⟨h₁,h₂,?_⟩
  have ha : (Z∪(profileRootSet σ).map e).card ≤ Z.card+∑ j,a j := by
    simpa only [Finset.card_map,profileRootSet_card] using Finset.card_union_le Z ((profileRootSet σ).map e)
  rw [← Finset.union_sdiff_self_eq_union]
  have hh := Finset.card_union_le (Z∪(profileRootSet σ).map e)
    ((Z∪(profileRootSet τ).map e)\(Z∪(profileRootSet σ).map e))
  omega

end Oberwolfach
