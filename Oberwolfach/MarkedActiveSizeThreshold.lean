module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Fixed active-set size requirements hold once the terminal scale is
sufficiently large, with the threshold chosen after the vortex ratio. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_size_threshold (ρ₀ ε:ℝ) (hρ:0<ρ₀) (he:0<ε) (M N:ℕ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ m:ℕ,m₀≤m→
      (N:ℝ)≤3*ε*m/8 ∧ (M:ℝ)≤3*ε*m/8 ∧ (M:ℝ)≤9*ρ₀*ε*m/256:=by
  let a:ℝ:=3*ε/8
  let b:ℝ:=9*ρ₀*ε/256
  have ha:0<a:=by dsimp [a];positivity
  have hb:0<b:=by dsimp [b];positivity
  obtain ⟨m₀,hm₀⟩:=exists_nat_gt ((N:ℝ)/a+(M:ℝ)/a+(M:ℝ)/b+1)
  refine ⟨max 1 m₀,le_max_left _ _,?_⟩
  intro m hm
  have hm':(m₀:ℝ)≤m:=by exact_mod_cast (le_trans (le_max_right _ _) hm)
  have hsum:(N:ℝ)/a+(M:ℝ)/a+(M:ℝ)/b+1≤m:=le_trans hm₀.le hm'
  have hN0:0≤(N:ℝ)/a:=div_nonneg (Nat.cast_nonneg _) ha.le
  have hM0:0≤(M:ℝ)/a:=div_nonneg (Nat.cast_nonneg _) ha.le
  have hMb0:0≤(M:ℝ)/b:=div_nonneg (Nat.cast_nonneg _) hb.le
  have hN:(N:ℝ)/a≤m:=by linarith
  have hM:(M:ℝ)/a≤m:=by linarith
  have hMb:(M:ℝ)/b≤m:=by linarith
  have hNa:=(div_le_iff₀ ha).mp hN
  have hMa:=(div_le_iff₀ ha).mp hM
  have hMb':=(div_le_iff₀ hb).mp hMb
  dsimp [a,b] at hNa hMa hMb'
  refine ⟨?_,?_,?_⟩ <;> nlinarith [hNa,hMa,hMb']
end Oberwolfach
