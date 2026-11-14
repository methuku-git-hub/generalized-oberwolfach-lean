module

public import Oberwolfach.OrdinaryPlacementEarlyRateData
public import Oberwolfach.MarkedInitialInnerHubBound

@[expose] public section
/-! The vortex contraction already selected below the early geometry scale
fits the capacity bound needed for the first hub set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_early_scale_le_placement_capacity
    (γ ρ₀ smin capInner β lamList ζList εearly ε:ℝ) (dMin:ℕ)
    (hρ:0<ρ₀) (hs:0<smin)
    (hEarly:OrdinaryPlacementEarlyRateData γ ρ₀ smin capInner β lamList ζList εearly dMin)
    (hε:0≤ε) (hεearly:ε≤εearly):
    let αcap:=5*ρ₀*smin^2/128;
    0<αcap ∧ ε≤αcap ∧
    ∀{n q D mv:ℕ} (P:SimpleGraph (Fin n)) (βv:ℝ) (Q:Vortex (Fin q) P D βv ε mv),
      q≤n → ((Q.extendedIndices 1).card:ℝ)≤αcap*n :=by
  intro αcap
  have hα:0<αcap:=by dsimp [αcap];positivity
  obtain ⟨_,_,_,_,_,_,_,_,_,hfloor,_,_,_,_⟩:=hEarly
  have ha:min (1/1024:ℝ) (min (αcap/4096) (1/2:ℝ)/8)≤min (αcap/4096) (1/2:ℝ)/8:=min_le_right _ _
  have hb:min (αcap/4096) (1/2:ℝ)≤αcap/4096:=min_le_left _ _
  have he:ε≤αcap:=by linarith
  refine ⟨hα,he,?_⟩
  intro n q D mv P βv Q hq
  have hh:=marked_initial_inner_hub_bound P D mv βv ε Q hε (by simpa using hq)
  simp only [Fintype.card_fin] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right he (by positivity))
end Oberwolfach
