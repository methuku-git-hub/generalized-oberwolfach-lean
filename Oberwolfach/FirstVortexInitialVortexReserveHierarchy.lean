module

public import Oberwolfach.FirstVortexInitialMatchingVortexChoice

@[expose] public section
/-! Choose the terminal-list reserve before the ambient cap and vortex scale,
using the exact list density of the common matching selector. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_initial_vortex_reserve_hierarchy
    (αRef ρ₀:ℝ) (hα:0<αRef) (hρ:0<ρ₀):
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃βfinal ρreserve:ℝ,0<βfinal ∧ βfinal≤1 ∧ βfinal≤βList/4 ∧ 0<ρreserve ∧
      βfinal+2*ρreserve≤βList/2 ∧
      (∀e:ℕ,∃N:ℕ,∀n:ℕ,N≤n→(e:ℝ)≤ρreserve*n) ∧
    ∀δglobal εLevel εInner εAbs εRob γRich kstar tstar:ℝ,
      0<δglobal→0<εLevel→0<εInner→0<εAbs→0<εRob→0<γRich→0<kstar→0<tstar→
    ∃bmatch α ε:ℝ,0<bmatch ∧ bmatch≤((ρ₀/4)/40000)/16 ∧
      0<α ∧ (2*α)/16≤bmatch ∧ 2*α≤4*δglobal ∧
      0<ε ∧ ε<1/4 ∧ ε≤εLevel ∧ ε≤εInner ∧ ε≤εAbs ∧ ε≤εRob ∧ ε≤βList/32 ∧
      ε≤min ((γRich/2)*kstar) tstar/128 ∧ ε≤(2*α)/100000 ∧
      ε≤α/1000 ∧ ε≤(ρ₀/4)/80000 ∧ ε≤((ρ₀/4)/40000)/8192 ∧
      ε≤δglobal ∧ βfinal+ε≤βList :=by
  intro βList
  have hList:0<βList:=by dsimp [βList];positivity
  let βfinal:=min (βList/8) (1/2:ℝ)
  let ρreserve:=βList/32
  have hβ:0<βfinal:=by dsimp [βfinal];positivity
  have hβ1:βfinal≤1:=by dsimp [βfinal];have hh:=min_le_right (βList/8) (1/2:ℝ);linarith
  have hβList:βfinal≤βList/4:=by dsimp [βfinal];have hh:=min_le_left (βList/8) (1/2:ℝ);linarith
  have hreserve:0<ρreserve:=by dsimp [ρreserve];positivity
  have hReserveBudget:βfinal+2*ρreserve≤βList/2:=by
    have hh:βfinal≤βList/8:=min_le_left _ _
    dsimp [ρreserve]
    linarith
  refine ⟨βfinal,ρreserve,hβ,hβ1,hβList,hreserve,hReserveBudget,?_,?_⟩
  · intro e
    obtain ⟨N,hN⟩:=exists_nat_ge ((e:ℝ)/ρreserve)
    refine ⟨N,?_⟩
    intro n hn
    have hn':(N:ℝ)≤n:=by exact_mod_cast hn
    simpa only [mul_comm] using (div_le_iff₀ hreserve).mp (hN.trans hn')
  · intro δglobal εLevel εInner εAbs εRob γRich kstar tstar hδ hLevel hInner hAbs hRob hγ hk ht
    exact first_vortex_initial_matching_vortex_choice ρ₀ δglobal βList βfinal εLevel εInner εAbs εRob γRich kstar tstar (βList/32)
      hρ hδ hList hβ.le hβList hLevel hInner hAbs hRob hγ hk ht (by positivity)
end Oberwolfach
