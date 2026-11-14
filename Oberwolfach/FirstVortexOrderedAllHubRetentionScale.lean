module

public import Oberwolfach.FirstVortexOrderedRetentionChoice
public import Oberwolfach.FirstVortexGlobalRetentionToLocal

@[expose] public section
/-! The ordered retention choice simultaneously gives the residual-size
budget and, on the same retained sample, a local test at every hub. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
local instance orderedRetentionScaleDecEq {V:Type}:DecidableEq V:=Classical.decEq _

theorem first_vortex_ordered_all_hub_retention_scale
    (ε cap θ:ℝ) (m d:ℕ) (hε:0<ε) (hε1:ε≤1) (hcap:0<cap) (hθ:0<θ)
    (hm:0<m) (hd:1≤d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃ζglobal ζlocal:ℝ,0<ζglobal ∧ 0<ζlocal ∧
      ζglobal≤θ/4096 ∧ ζlocal≤cap/128 ∧ ζglobal≤ζlocal*ε/2 ∧
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
  obtain ⟨ζglobal,ζlocal,hglobal,hlocal,hθζ,hcapζ,hscale,N,hN⟩:=
    first_vortex_ordered_retention_choice ε cap θ m d hε hcap hθ hm hd hspacing
  refine ⟨ζglobal,ζlocal,hglobal,hlocal,hθζ,hcapζ,hscale,⟨N,hN⟩,?_⟩
  intro V U Γ Color _ _ _ _ _ _ G D mm β Q hmm π σ g t J hgood
  exact first_vortex_global_retention_to_local G D mm β ε Q hε hε1 hmm π d σ g t J ζglobal ζlocal hlocal.le hscale hgood
end Oberwolfach
