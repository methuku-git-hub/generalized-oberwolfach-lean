module

public import Mathlib.Tactic

@[expose] public section
/-! The terminal-list margin and bounded reserve are chosen before the
absorber size, with the order threshold chosen afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_terminal_list_reserve_choice
    (βList:ℝ) (hβ:0<βList):
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      ∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n :=by
  let βfinal:ℝ:=min (βList/4) (1/2)
  let ρreserve:ℝ:=βList/16
  have hfinal:0<βfinal:=by dsimp [βfinal]; positivity
  have hreserve:0<ρreserve:=by dsimp [ρreserve]; positivity
  have hfinal1:βfinal≤1:=by dsimp [βfinal]; have :=min_le_right (βList/4) (1/2:ℝ); linarith
  have hfinalβ:βfinal≤βList/4:=min_le_left _ _
  refine ⟨βfinal,ρreserve,hfinal,hfinal1,hreserve,?_,?_⟩
  · dsimp [ρreserve];linarith
  · intro e
    obtain ⟨N,hN⟩:=exists_nat_ge ((e:ℝ)/ρreserve)
    refine ⟨N,?_⟩
    intro n hn
    have hnn:(N:ℝ)≤n:=by exact_mod_cast hn
    have hbound:(e:ℝ)/ρreserve≤n:=hN.trans hnn
    simpa only [mul_comm] using (div_le_iff₀ hreserve).mp hbound
end Oberwolfach
