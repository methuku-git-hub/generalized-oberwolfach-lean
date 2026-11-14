module

public import Oberwolfach.LongSeedFailureUniform
public import Oberwolfach.LongAssignedSpokeFailureUniform

@[expose] public section
/-! The original seed-concentration and hub-count errors are jointly small
for one order threshold chosen before the hub set and the sample. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem eventually_assigned_seed_spoke_failure_below
    (d m K:ℕ) (ℓ:Fin K→ℕ) (BM:ℝ) (BO:Fin K→ℝ) (t ξ δ:ℝ)
    (hBM:0<BM) (hBO:∀i,0<BO i) (ht:0<t) (hξ:0<ξ) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀U:Type,[Fintype U]→Fintype.card U≤n→
      4*(Fintype.card U:ℝ)*Real.exp
        (-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ)))+
      mixedSeedFailureBound (Fin n) U d m K ℓ BM BO t<δ :=by
  have hd:0<δ/2:=by positivity
  obtain ⟨N₁,h₁⟩:=eventually_assigned_spoke_failure_below d ξ (δ/2) hξ hd
  obtain ⟨N₂,h₂⟩:=eventually_named_mixed_seed_failure_below d m K ℓ BM BO t (δ/2) hBM hBO ht hd
  refine ⟨max N₁ N₂,?_⟩
  intro n hn U _ hu
  have ha:=h₁ n ((le_max_left _ _).trans hn) U hu
  have hb:=h₂ n ((le_max_right _ _).trans hn) U hu
  linarith
end Oberwolfach
