module

public import Oberwolfach.OrdinaryBoundaryLoadSpacing

@[expose] public section

/-! The local concentration error is eventually below any fixed positive
placement rate, uniformly over all inner subsets of the ambient vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_inner_target_fluctuation_eventually
    (z:ℝ) (hz:0<z):
    ∃N:ℕ,∀n:ℕ,N≤n→∀Inner:Finset (Fin n),
      (Inner.card:ℝ)^(3/4:ℝ)≤z*n/16 :=by
  obtain ⟨d,N,hd,hN,hbound⟩:=ordinary_boundary_load_spacing_and_order z hz
  refine ⟨N,?_⟩
  intro n hn Inner
  have hcardNat:Inner.card≤n:=by simpa only [Fintype.card_fin] using Finset.card_le_univ Inner
  have hcard:(Inner.card:ℝ)≤n:=by exact_mod_cast hcardNat
  have hpow:=Real.rpow_le_rpow (Nat.cast_nonneg Inner.card) hcard (by norm_num:(0:ℝ)≤3/4)
  have hNpow:4*(n:ℝ)^(3/4:ℝ)≤z*n/16:=(hbound d (le_refl _) n hn).2
  have hp0:0≤(n:ℝ)^(3/4:ℝ):=by positivity
  nlinarith
end Oberwolfach
