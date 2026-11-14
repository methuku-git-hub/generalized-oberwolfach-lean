module

public import Oberwolfach.LongOriginalSeedMatchingMargin

@[expose] public section
/-! The seed length can be chosen after an arbitrary lower bound, using only
the original positive degree margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_seed_length_original_margin
    (L:ℕ) (α:ℝ) (hα:0<α):
    ∃m k:ℕ,L≤m ∧ 7≤m ∧ Even (m+1) ∧ m+1=(k+2)*2 ∧
      successorCycleRatio k+α/2≤1/2+α :=by
  obtain ⟨N,_hN,hmargin⟩:=long_original_seed_matching_margin α 1 hα (by norm_num)
  let m:=2*(max L N+4)+1
  have hm:7≤m:=by dsimp [m];omega
  have hN:N≤m:=by dsimp [m];omega
  have hL:L≤m:=by dsimp [m];omega
  have heven:Even (m+1):=by
    refine ⟨max L N+5,?_⟩
    dsimp [m]
    omega
  obtain ⟨r,k,hr,hrm,hlen,hcycle,_⟩:=hmargin m hN hm heven
  refine ⟨m,k,hL,hm,heven,?_,hcycle⟩
  omega
end Oberwolfach
