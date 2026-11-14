module

public import Oberwolfach.MarkedIterationToleranceChoices

@[expose] public section
set_option autoImplicit false
namespace Oberwolfach

theorem marked_iteration_global_tolerance_choice_uniform_densities
    (r h:ℕ) (κ γ p₀ k₀ omega₀ C θ b₀:ℝ)
    (hκ:0<κ) (hγ:0<γ) (hp₀:0<p₀) (hk₀:0<k₀) (ho₀:0<omega₀)
    (hC:0≤C) (hθ:0<θ) (hb₀:0<b₀):
    ∃ ζmax:ℝ,0<ζmax ∧ ∀ p k omega b:ℝ,p₀≤p → k₀≤k → omega₀≤omega → b₀≤b →
      ∀ ε ζ:ℝ,ε≤κ/4 → 0≤ζ → ζ≤ζmax →
      ε+ζ≤κ ∧ ε+4*ζ≤κ ∧ ε+2*h*ζ≤κ ∧ ε+h*ζ≤κ ∧
      ζ≤(κ-ε)*omega ∧ ε≤κ ∧ 2*ζ≤(3/4)*γ*p^2 ∧ ζ≤γ*min p k/8 ∧
      C*ζ≤κ/4 ∧ C*ζ≤θ/4 ∧ 2*(r+5:ℝ)*ζ≤b ∧ (2*r+11:ℝ)*ζ≤b :=by
  obtain ⟨z,hz,hbase⟩:=marked_iteration_global_tolerance_choice r h κ γ p₀ k₀ omega₀ C θ b₀ hκ hγ hp₀ hk₀ ho₀ hC hθ hb₀
  refine ⟨z,hz,?_⟩
  intro p k omega b hp hk ho hb ε ζ he hz0 hzmax
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩:=hbase ε ζ he hz0 hzmax
  have hp0:0≤p:=hp₀.le.trans hp
  have hp2:p₀^2≤p^2:=by nlinarith [sq_nonneg (p-p₀)]
  have hmin:min p₀ k₀≤min p k:=min_le_min hp hk
  have hω:=mul_le_mul_of_nonneg_left ho (show 0≤κ-ε by linarith)
  have hγp:=mul_le_mul_of_nonneg_left hp2 (show 0≤(3/4:ℝ)*γ by positivity)
  have hγm:=mul_le_mul_of_nonneg_left hmin hγ.le
  refine ⟨h1,h2,h3,h4,h5.trans hω,h6,h7.trans hγp,?_,h9,h10,h11.trans hb,h12.trans hb⟩
  nlinarith only [h8,hγm]

theorem marked_iteration_local_tolerance_choice_uniform_density
    (m h:ℕ) (x eps C t₀ β η:ℝ)
    (hx:0<x) (heps:0<eps) (hC:0≤C) (ht₀:0<t₀) (hβ:0<β) (hη:0<η):
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ t:ℝ,t₀≤t → ∀ sigma:ℝ,0≤sigma→sigma≤sigmaMax→
      (m+2:ℝ)*sigma≤x/4 ∧ 2*(h:ℝ)*sigma≤x/2 ∧
      4*C*sigma/eps≤min (t/8) (min β (η/4)):=by
  obtain ⟨s,hs,hbase⟩:=marked_iteration_local_tolerance_choice m h x eps C t₀ β η hx heps hC ht₀ hβ hη
  refine ⟨s,hs,?_⟩
  intro t ht sigma hsigma hmax
  obtain ⟨h1,h2,h3⟩:=hbase sigma hsigma hmax
  exact ⟨h1,h2,h3.trans (min_le_min (by linarith) le_rfl)⟩
end Oberwolfach
