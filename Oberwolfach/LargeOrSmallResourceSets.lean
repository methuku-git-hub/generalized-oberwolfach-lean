module

public import Oberwolfach.FractionalResourceMatching

@[expose] public section
/-! A matching that covers all large incident resource sets also leaves
few resources in every small incident set, deterministically. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq W]

theorem all_resource_sets_from_large_sets
    (S:V→Finset W) (covered:Finset W) (n a γ B:ℝ)
    (hn:0≤n) (hγ:0≤γ) (hB:0≤B)
    (hsize:∀v,((S v).card:ℝ)≤B*n)
    (hlarge:∀v,a*n≤(S v).card → (((S v)\covered).card:ℝ)≤γ*(S v).card):
    ∀v,(((S v)\covered).card:ℝ)≤max a (γ*B)*n := by
  intro v
  have hsubset:((S v\covered).card:ℝ)≤(S v).card := by
    exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset : S v\covered ⊆ S v))
  have hamax:a≤max a (γ*B):=le_max_left _ _
  have hbmax:γ*B≤max a (γ*B):=le_max_right _ _
  by_cases hv:a*n≤(S v).card
  · have hh:=hlarge v hv
    have hh' : γ*((S v).card:ℝ)≤γ*(B*n) := mul_le_mul_of_nonneg_left (hsize v) hγ
    have hh'' : γ*B*n≤max a (γ*B)*n := mul_le_mul_of_nonneg_right hbmax hn
    nlinarith
  · have hh : (S v).card≤a*n := le_of_lt (lt_of_not_ge hv)
    have hh' := mul_le_mul_of_nonneg_right hamax hn
    linarith
end Oberwolfach
