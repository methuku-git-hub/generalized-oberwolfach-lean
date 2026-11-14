module

public import Oberwolfach.DisjointPairSwitches
public import Oberwolfach.DisjointPatternSampling

@[expose] public section

/-! Recolouring a prescribed finite set of distinct physical edges. The
change in every tested sum is computed on the original fixed coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def recolourCoordinates {I E C : Type*} [Fintype I] [DecidableEq E]
    (ι : I↪E) (σ : E → C) (c : I → C) (e : E) : C :=
  if he : e∈Set.range ι then c (ι.toEquivRange.symm ⟨e,he⟩) else σ e

theorem recolourCoordinates_image {I E C : Type*} [Fintype I] [DecidableEq E]
    (ι : I↪E) (σ : E → C) (c : I → C) (i : I) :
    recolourCoordinates ι σ c (ι i)=c i := by
  simp [recolourCoordinates]

theorem recolourCoordinates_fixed {I E C : Type*} [Fintype I] [DecidableEq E]
    (ι : I↪E) (σ : E → C) (c : I → C) (e : E) (he : e∉Set.range ι) :
    recolourCoordinates ι σ c e=σ e := by simp [recolourCoordinates,he]

theorem recolour_weighted_difference {I E C R : Type*}
    [Fintype I] [Fintype E] [DecidableEq E] [CommRing R]
    (ι : I↪E) (σ : E → C) (c : I → C) (t : E → R) (g : C → R) :
    (∑ e,t e*g (recolourCoordinates ι σ c e))-(∑ e,t e*g (σ e))=
      ∑ i,t (ι i)*(g (c i)-g (σ (ι i))) := by
  rw [← Finset.sum_sub_distrib]
  rw [sum_supported_embedding ι _ (by
    intro e he
    rw [recolourCoordinates_fixed ι σ c e he,sub_self])]
  apply Finset.sum_congr rfl
  intro i _
  rw [recolourCoordinates_image]
  ring

theorem disjoint_pattern_stability {E I : Type*} [DecidableEq E]
    {State : E → Type*} (C : Finset I) (F : I → Finset E)
    (s : I → ∀ e,State e) (D : Finset E) (σ τ : ∀ e,State e)
    (hdisj : ∀ i∈C,∀ j∈C,i≠j → Disjoint (F i) (F j))
    (h : ∀ e,e∉D → σ e=τ e) :
    |(∑ i∈C,patternValue (F i) (s i) τ)-(∑ i∈C,patternValue (F i) (s i) σ)|≤D.card := by
  have hh := weighted_product_stability C F s (fun _ => 1) D σ τ (by intros;norm_num)
    (fun i hi e he heD => h e heD)
  simp only [one_mul] at hh
  apply hh.trans
  have hi (e : E) : (∑ i∈C,if e∈F i then (1:ℝ) else 0)≤1 := by
    classical
    have hcard : (C.filter (fun i => e∈F i)).card≤1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      exact Finset.disjoint_left.mp (hdisj i (Finset.mem_filter.mp hi).1 j
        (Finset.mem_filter.mp hj).1 hij) (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    have heq : (∑ i∈C,if e∈F i then (1:ℝ) else 0)=((C.filter (fun i => e∈F i)).card:ℝ) := by
      simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    rw [heq]
    exact_mod_cast hcard
  calc
    _ ≤ ∑ _e∈D,(1:ℝ) := Finset.sum_le_sum (fun e _ => hi e)
    _ = _ := by simp

end Oberwolfach
