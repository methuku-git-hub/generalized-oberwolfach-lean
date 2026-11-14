module

public import Oberwolfach.FirstVortexOrderedAllHubRetentionScale

@[expose] public section
/-! The earlier global retention error simultaneously meets the first-inner
scale and the global correction cap. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
local instance orderedRetentionBudgetDecEq {V:Type}:DecidableEq V:=Classical.decEq _

theorem first_vortex_ordered_all_hub_retention_budget
    (ε cap θ:ℝ) (m d:ℕ) (hε:0<ε) (hε1:ε≤1/4) (hcap:0<cap) (hθ:0<θ)
    (hm:0<m) (hd:1≤d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃ζglobal ζlocal:ℝ,0<ζglobal ∧ 0<ζlocal ∧
      ζglobal≤θ/4096 ∧ ζlocal≤cap/128 ∧ ζglobal≤ζlocal*ε/2 ∧
      ζglobal≤min cap (1:ℝ)/1024 ∧
      (∃N:ℕ,∀n:ℕ,N≤n→∀q errOrd:ℝ,
        q≤1/((m:ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n)+errOrd≤4*θ*n) ∧
      ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
      ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J→
      RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J :=by
  let c:=min cap (1:ℝ)
  have hc:0<c:=by dsimp [c]; positivity
  obtain ⟨ζglobal,ζlocal,hglobal,hlocal,hθζ,hcapζ,hscale,hN,hRet⟩:=
    first_vortex_ordered_all_hub_retention_scale ε c θ m d hε (by linarith) hc hθ hm hd hspacing
  have hlocalcap:ζlocal≤cap/128:=by
    have :=min_le_left cap (1:ℝ)
    dsimp only [c] at hcapζ
    linarith
  have hbudget:ζglobal≤min cap (1:ℝ)/1024:=by
    have hc0:0≤c:=hc.le
    have hprod:=mul_le_mul_of_nonneg_right hcapζ hε.le
    dsimp only [c] at hprod
    nlinarith [mul_nonneg hc0 (show 0≤(1/4:ℝ)-ε by linarith)]
  exact ⟨ζglobal,ζlocal,hglobal,hlocal,hθζ,hlocalcap,hscale,hbudget,hN,hRet⟩
end Oberwolfach
