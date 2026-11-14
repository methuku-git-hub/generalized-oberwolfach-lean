module

public import Oberwolfach.MarkedVortexCutDeepHierarchy

@[expose] public section
/-! Choose the vortex ratio and inner-density lower bound before invoking the
cover-down theorem, uniformly for all admissible subsequent densities. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_vortex_uniform_early_geometry
    (r : ℕ) (α kstar tstar ζ ρ₀ κ ξcap K : ℝ)
    (hα : 0 < α) (hk : 0 < kstar) (ht : 0 < tstar)
    (hζ : ζ ≤ tstar / 16) (hρ₀ : 0 < ρ₀) (hκ : 0 < κ)
    (hξ : 0 < ξcap) (hK : 0 ≤ K) :
    ∃ hcut ε₀ δ : ℝ,
      0 < hcut ∧ 2*hcut ≤ α*kstar/4 ∧ 2*hcut ≤ tstar/8-ζ ∧
      0 < ε₀ ∧ ε₀ ≤ hcut ∧ 4*ε₀ ≤ ξcap ∧ ε₀ ≤ κ ∧ ε₀ ≤ α/8 ∧ ε₀ ≤ 1/8 ∧
      0 < δ ∧ δ < 1/4 ∧ δ ≤ α/32 ∧ δ ≤ kstar/32 ∧ 2*δ ≤ tstar/8 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ ω ξ : ℝ, 0 < ω ∧ ω ≤ 1 ∧ 0 < ξ ∧
          ω ≤ ε/8 ∧ ω ≤ ρ₀*ε/64 ∧ ε^2 ≤ ξ ∧ ξ ≤ ξcap ∧
          (4*K+(3*r+50:ℕ))*ξ ≤ κ/2 ∧
          ∀ ρ t : ℝ, ρ₀ ≤ ρ → tstar ≤ t →
            (1+2/ρ)*ξ ≤ t*ω/32 := by
  obtain ⟨hcut, ε₀, hh, _, hp, hs, he, hecap, hecut, hdelta, hchoose⟩ :=
    marked_vortex_cut_deep_hierarchy r α kstar tstar ζ 1 ρ₀ ρ₀ tstar κ ξcap K
      (min (ξcap/4) (min κ (min (α/8) (1/8)))) hα hk ht hζ (by norm_num) hρ₀ hρ₀ ht hκ hξ hK (by positivity)
  obtain ⟨δ, hδ, _, hδlt, hδα, hδk, hδt⟩ := hdelta (1/8) (by norm_num)
  have heξ : 4*ε₀ ≤ ξcap := by
    have hh := hecap.trans (min_le_left (ξcap/4) (min κ (min (α/8) (1/8))))
    linarith
  refine ⟨hcut, ε₀, δ, hh, hp, hs, he, hecut, heξ,
    (hecap.trans (min_le_right _ _)).trans (min_le_left _ _),
    ((hecap.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _),
    ((hecap.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _),
    hδ, hδlt, hδα, hδk, hδt, ?_⟩
  intro ε hε hεcap
  obtain ⟨ω, ξ, hω, hω1, hξ', hωv, hωu, hξlow, hξhi, hscale, hgap⟩ :=
    hchoose ε hε hεcap
  refine ⟨ω, ξ, hω, hω1, hξ', hωv, hωu, hξlow, hξhi, hscale, ?_⟩
  intro ρ t hρ ht'
  have hρpos : 0 < ρ := lt_of_lt_of_le hρ₀ hρ
  have hdiv : 2/ρ ≤ 2/ρ₀ := div_le_div_of_nonneg_left (by norm_num) hρ₀ hρ
  have hleft : (1+2/ρ)*ξ ≤ (1+2/ρ₀)*ξ := by
    exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hξ')
  have hright : tstar*ω/32 ≤ t*ω/32 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right ht' (le_of_lt hω)
  exact hleft.trans (hgap.trans hright)
end Oberwolfach
