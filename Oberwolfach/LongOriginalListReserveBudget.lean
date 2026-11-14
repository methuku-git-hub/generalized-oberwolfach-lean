module

public import Mathlib.Tactic

@[expose] public section
/-! The reserve budget and final list margin can be chosen from the original
    positive density and degree margin, before the finite absorber size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_original_list_reserve_budget
    (αRef ρ₀:ℝ) (hα:0<αRef) (hρ:0<ρ₀):
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃βfinal ρreserve:ℝ, 0<βfinal ∧ βfinal≤1 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      ∀e₀:ℕ, ∃N:ℕ, ∀n:ℕ,N≤n→(e₀:ℝ)≤ρreserve*n :=by
  intro βList
  have hList:0<βList:=by dsimp [βList];positivity
  let βfinal:ℝ:=min (βList/4) (1/2:ℝ)
  let ρreserve:ℝ:=βList/16
  have hFinal:0<βfinal:=by dsimp [βfinal];positivity
  have hFinalList:βfinal≤βList/4:=min_le_left _ _
  have hFinalOne:βfinal≤1:=by
    have h:=min_le_right (βList/4) (1/2:ℝ)
    dsimp [βfinal];linarith
  have hReserve:0<ρreserve:=by dsimp [ρreserve];positivity
  refine ⟨βfinal,ρreserve,hFinal,hFinalOne,hReserve,?_,?_⟩
  · dsimp [ρreserve];linarith
  · intro e₀
    obtain ⟨N,hN⟩:=exists_nat_ge ((e₀:ℝ)/ρreserve)
    refine ⟨N,?_⟩
    intro n hn
    have hn':(N:ℝ)≤n:=by exact_mod_cast hn
    have h:=hN.trans hn'
    have h':(e₀:ℝ)≤(n:ℝ)*ρreserve:=(div_le_iff₀ hReserve).mp h
    nlinarith
end Oberwolfach
