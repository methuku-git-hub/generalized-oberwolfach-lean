module

public import Oberwolfach.LongResidualVortexClassCapChoice

@[expose] public section
/-! Select the residual class tolerance required by the concrete boundary
adapter uniformly for all smaller real errors, including negative bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem long_boundary_prepared_numeric_cap_choice
    (α lam lamAssign ε δold δlocal ρ₀ θ:ℝ)
    (hα:0<α) (hε:0<ε) (hlam:lam<lamAssign) (hδ:δold<δlocal)
    (htiny:lam<((ρ₀/4)/40000)*θ/4096):
    ∃ξCap:ℝ,0<ξCap ∧ ∀ξ':ℝ,ξ' ≤ ξCap  → 
      lam+ξ' ≤ ((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2 ≤ (lamAssign-lam)*ε ∧ ξ' ≤ α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mv:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mv),0<mv  → 
        ξ'*(n:ℝ) ≤ (δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨base,hbase,hprops⟩:=long_residual_vortex_class_cap_choice α lam lamAssign ε δold δlocal hα hε hlam hδ
  let slack:ℝ:=((ρ₀/4)/40000)*θ/4096-lam
  have hslack:0<slack:=by dsimp [slack];linarith
  let cap:ℝ:=min base (min (slack/2) (α/64))
  have hcap:0<cap:=by dsimp [cap];positivity
  have hcapBase:cap ≤ base:=min_le_left _ _
  have hcapSlack:cap ≤ slack/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hcapAlpha:cap ≤ α/64:=(min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨_,hedge,hinner⟩:=hprops cap hcap.le hcapBase
  refine ⟨cap,hcap,?_⟩
  intro ξ' hξ'
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [slack] at hcapSlack
    linarith
  · linarith
  · linarith
  · intro n U _ G D mv β Q hmv
    have hh:=mul_le_mul_of_nonneg_right hξ' (show (0:ℝ) ≤ n by positivity)
    exact hh.trans (hinner n U G D mv β Q hmv)
end Oberwolfach
