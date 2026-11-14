module

public import Oberwolfach.SubsetMean

@[expose] public section

/-! Exchanging two labels changes every fixed intersection count by at most one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem swap_subset_new_card_le_one {V : Type*} (S : Finset V) (u v : V) :
    ((S.map (Equiv.swap u v).toEmbedding) \ S).card ≤ 1 := by
  by_cases hu : u ∈ S
  · have hsub : (S.map (Equiv.swap u v).toEmbedding) \ S ⊆ {v} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_map_equiv, Equiv.symm_swap] at hx
      apply Finset.mem_singleton.mpr
      by_contra hxv
      have hxu : x ≠ u := by intro h; subst x; exact hx.2 hu
      have he : Equiv.swap u v x = x := Equiv.swap_apply_of_ne_of_ne hxu hxv
      exact hx.2 (by simpa only [he] using hx.1)
    simpa only [Finset.card_singleton] using Finset.card_le_card hsub
  · have hsub : (S.map (Equiv.swap u v).toEmbedding) \ S ⊆ {u} := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_map_equiv, Equiv.symm_swap] at hx
      apply Finset.mem_singleton.mpr
      by_contra hxu
      by_cases hxv : x = v
      · subst x
        exact hu (by simpa using hx.1)
      · have he : Equiv.swap u v x = x := Equiv.swap_apply_of_ne_of_ne hxu hxv
        exact hx.2 (by simpa only [he] using hx.1)
    simpa only [Finset.card_singleton] using Finset.card_le_card hsub

theorem swap_subset_intersection_change {V : Type*} (A S : Finset V) (u v : V) :
    |((A ∩ S).card : ℝ) - (A ∩ S.map (Equiv.swap u v).toEmbedding).card| ≤ 1 := by
  let T := S.map (Equiv.swap u v).toEmbedding
  have hinv : T.map (Equiv.swap u v).toEmbedding = S := by
    ext x
    simp [T]
  have hn : (T \ S).card ≤ 1 := swap_subset_new_card_le_one S u v
  have ho : (S \ T).card ≤ 1 := by
    have hh := swap_subset_new_card_le_one T u v
    rw [hinv] at hh
    exact hh
  have hsub (B C : Finset V) : (A ∩ B) \ (A ∩ C) ⊆ B \ C := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_inter] at hx ⊢
    exact ⟨hx.1.2, fun hc => hx.2 ⟨hx.1.1, hc⟩⟩
  have h1 : (A ∩ S).card ≤ (A ∩ T).card + 1 := by
    have h := Finset.card_le_card_sdiff_add_card (s := A ∩ S) (t := A ∩ T)
    have hsmall := (Finset.card_le_card (hsub S T)).trans ho
    omega
  have h2 : (A ∩ T).card ≤ (A ∩ S).card + 1 := by
    have h := Finset.card_le_card_sdiff_add_card (s := A ∩ T) (t := A ∩ S)
    have hsmall := (Finset.card_le_card (hsub T S)).trans hn
    omega
  have h1r : ((A ∩ S).card : ℝ) ≤ (A ∩ T).card + 1 := by exact_mod_cast h1
  have h2r : ((A ∩ T).card : ℝ) ≤ (A ∩ S).card + 1 := by exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Oberwolfach
