module

public import Oberwolfach.LongRawIncidenceSizes
public import Oberwolfach.LongRawMatchingAllIncidences

@[expose] public section
/-! Convert the matching's simultaneous incidence estimates into explicit
linear bounds for each auxiliary endpoint and each typed spoke incidence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_matching_incidence_linear_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (Covered:Finset S) (a γ:ℝ) (hγ:0≤γ)
    (hu:Fintype.card U≤n)
    (h:∀i,((longRawIncidenceSet S i\Covered).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card)):
    (∀x,((longRawIncidenceSet S (.inl x)\Covered).card:ℝ)≤max a (4*γ)*n) ∧
    (∀typ x,((longRawIncidenceSet S (.inr (typ,.inl x))\Covered).card:ℝ)≤max a γ*n) ∧
    (∀typ u,((longRawIncidenceSet S (.inr (typ,.inr u))\Covered).card:ℝ)≤max a γ*n) :=by
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have hau:∀x,γ*((longRawIncidenceSet S (.inl x)).card:ℝ)≤(4*γ)*n:=by
    intro x
    have hh:((longRawIncidenceSet S (.inl x)).card:ℝ)≤4*(n:ℝ):=by
      exact_mod_cast long_raw_auxiliary_incidence_card_le S x
    nlinarith [mul_le_mul_of_nonneg_left hh hγ]
  have hv:∀typ x,γ*((longRawIncidenceSet S (.inr (typ,.inl x))).card:ℝ)≤γ*n:=by
    intro typ x
    have hh:((longRawIncidenceSet S (.inr (typ,.inl x))).card:ℝ)≤n:=by
      exact_mod_cast (long_raw_vertex_spoke_incidence_card_le S typ x).trans hu
    exact mul_le_mul_of_nonneg_left hh hγ
  have hh:∀typ u,γ*((longRawIncidenceSet S (.inr (typ,.inr u))).card:ℝ)≤γ*n:=by
    intro typ u
    have hc:((longRawIncidenceSet S (.inr (typ,.inr u))).card:ℝ)≤n:=by
      exact_mod_cast long_raw_hub_spoke_incidence_card_le S typ u
    exact mul_le_mul_of_nonneg_left hc hγ
  constructor
  · intro x
    apply (h (.inl x)).trans
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left a (4*γ)) hn
    · exact (hau x).trans (mul_le_mul_of_nonneg_right (le_max_right a (4*γ)) hn)
  constructor
  · intro typ x
    apply (h (.inr (typ,.inl x))).trans
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left a γ) hn
    · exact (hv typ x).trans (mul_le_mul_of_nonneg_right (le_max_right a γ) hn)
  · intro typ u
    apply (h (.inr (typ,.inr u))).trans
    apply max_le
    · exact mul_le_mul_of_nonneg_right (le_max_left a γ) hn
    · exact (hh typ u).trans (mul_le_mul_of_nonneg_right (le_max_right a γ) hn)
end Oberwolfach
