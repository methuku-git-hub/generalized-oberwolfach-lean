module

public import Mathlib.Tactic

@[expose] public section
/-! Select the common host size before the selector constants, then choose
the correction bound from those constants and combine the thresholds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_host_selector_threshold_order
    (vsize Nhost:ℕ) (S:Type) (eRob:S→ℕ)
    (Host:ℕ→Prop) (Select:ℕ→S→ℕ→ℕ→ℕ→Prop)
    (hHost:∀n:ℕ,Nhost≤n→Host n)
    (hSelect:∀size:ℕ,∃s:S,∀f₀ B:ℕ,∃N:ℕ,∀n:ℕ,N≤n→Select size s f₀ B n):
    ∃s:S,∀f₀:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
      Host n ∧ Select (2*vsize) s f₀ (eRob s) n :=by
  obtain ⟨s,hs⟩:=hSelect (2*vsize)
  refine ⟨s,?_⟩
  intro f₀
  obtain ⟨N,hN⟩:=hs f₀ (eRob s)
  refine ⟨max Nhost N,?_⟩
  intro n hn
  exact ⟨hHost n ((le_max_left _ _).trans hn),hN n ((le_max_right _ _).trans hn)⟩
end Oberwolfach
