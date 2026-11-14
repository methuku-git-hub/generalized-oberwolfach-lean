module

public import Oberwolfach.LongUnusedSpokeIncidence
public import Oberwolfach.LongRawMatchingIncidenceBounds

@[expose] public section
/-! Turn matching incidence estimates into uniform unused-spoke bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_unused_spoke_linear_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (covered:Finset S) (unused:U→Finset (Fin n))
    (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\covered).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrow:∀w,(unused w).card≤(longRawIncidenceSet S (.inr (false,.inr w))\covered).card)
    (hcol:∀v,(Finset.univ.filter (fun w=>v∈unused w)).card≤
      (longRawIncidenceSet S (.inr (false,.inl v))\covered).card):
    (∀w,((unused w).card:ℝ)≤max a γ*n) ∧
    (∀v,((Finset.univ.filter (fun w=>v∈unused w)).card:ℝ)≤max a γ*n):=by
  obtain ⟨_,hcol',hrow'⟩:=long_raw_matching_incidence_linear_bounds S covered a γ hγ hu hmatch
  constructor
  · intro w
    exact (Nat.cast_le.mpr (hrow w)).trans (hrow' false w)
  · intro v
    exact (Nat.cast_le.mpr (hcol v)).trans (hcol' false v)
end Oberwolfach
