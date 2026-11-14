module

public import Oberwolfach.LongSpokeChangeEventualBudget
public import Oberwolfach.LongSharedRimSpokeBudgetChoice

@[expose] public section
/-! A single large-sample threshold supplies both changes needed for the
corrected sample, including the two sublinear rim errors and the fixed
spoke error. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem long_shared_rim_spoke_eventual_budget
    (d:ℕ) (θ a γ ξClass δglobal Δ rho eta ζret refRate cap:ℝ) (hcap:0<cap):
    let c:=min cap (1:ℝ);
    (2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal+2*Δ+(1+2/rho)*eta<c/2048)→
    (2*(ζret+δglobal+Real.sqrt δglobal)+refRate+2*(c/1024)<c/2)→
    (2*(ζret+10*θ)+refRate≤c/2)→
    ∃N:ℕ,∀n:ℕ,N≤n→∀lossRow lossCol ε ηphys ηdel ηtype:ℝ,
      lossRow≤ζret*n→lossCol≤ζret*n→ε≤refRate*n→
      ηphys≤(2*θ+2*max a (4*γ)+2*ξClass+5*Real.sqrt δglobal)*n+
        (n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ)→
      ηdel≤Δ*n→ηtype≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)→
      ηphys+ηdel+ηtype≤cap*n ∧ c/2≤cap ∧
      2*(lossRow+(δglobal*n+(Real.sqrt δglobal*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤(c/2)*n ∧
      2*(lossCol+10*θ*n)+ε≤(c/2)*n :=by
  intro c hgap hrow hcol
  have hc:0<c:=by dsimp [c];exact lt_min hcap (by norm_num)
  have hccap:c≤cap:=min_le_left _ _
  have hcSmall:c/2048<c/1024:=by linarith
  obtain ⟨Nphys,hphys⟩:=long_corrected_change_graph_eventual_cap d θ a γ ξClass δglobal Δ 0 rho eta (c/1024)
    (by positivity) (hgap.trans hcSmall)
  obtain ⟨Nspoke,hspoke⟩:=long_spoke_change_eventual_budget δglobal θ ζret ζret refRate (c/1024) (c/2) hrow hcol
  refine ⟨max Nphys Nspoke,?_⟩
  intro n hn lossRow lossCol ε ηphys ηdel ηtype hlrow hlcol he hp hd ht
  have hphys':=((hphys n (by omega)).1)
  have hrim:ηphys+ηdel+ηtype≤(c/1024)*n:=by linarith only [hp,hd,ht,hphys']
  have hsp:=hspoke n (by omega) lossRow lossCol ε ηphys ηdel ηtype hlrow hlcol he hrim
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hcapRate:c/1024≤cap:=by linarith
  have hcapRim:=mul_le_mul_of_nonneg_right hcapRate hn0
  exact ⟨hrim.trans hcapRim,by linarith,hsp.1,hsp.2⟩
end Oberwolfach
