module

public import Oberwolfach.LongMatchingCorrectionSharedChangeCap

@[expose] public section
/-! Absorb the fixed error in the spoke-change estimate, using the same
linear rim-change bound that is used by the corrected record. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem long_spoke_change_eventual_budget
    (δ θ rowRate colRate refRate rimRate ζSpoke:ℝ)
    (hrow:2*(rowRate+δ+Real.sqrt δ)+refRate+2*rimRate<ζSpoke)
    (hcol:2*(colRate+10*θ)+refRate≤ζSpoke):
    ∃N:ℕ,∀n:ℕ,N≤n→∀lossRow lossCol ε ηphys ηdel ηtype:ℝ,
      lossRow≤rowRate*n→lossCol≤colRate*n→ε≤refRate*n→
      ηphys+ηdel+ηtype≤rimRate*n→
      2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤ζSpoke*n ∧
      2*(lossCol+10*θ*n)+ε≤ζSpoke*n :=by
  let c:=2*(rowRate+δ+Real.sqrt δ)+refRate+2*rimRate
  have hgap:0<ζSpoke-c:=by dsimp [c];linarith
  obtain ⟨N,hN⟩:=exists_nat_gt (2/(ζSpoke-c))
  refine ⟨N,?_⟩
  intro n hn lossRow lossCol ε ηphys ηdel ηtype hr hc he hp
  have hnreal:(N:ℝ)≤n:=by exact_mod_cast hn
  have hsub:2/(ζSpoke-c)<(n:ℝ):=hN.trans_le hnreal
  have hsub':2<(n:ℝ)*(ζSpoke-c):=(div_lt_iff₀ hgap).mp hsub
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hcol':(2*(colRate+10*θ)+refRate)*(n:ℝ)≤ζSpoke*n:=mul_le_mul_of_nonneg_right hcol hn0
  dsimp [c] at hsub'
  constructor <;> nlinarith only [hr,hc,he,hp,hsub',hcol']
end Oberwolfach
