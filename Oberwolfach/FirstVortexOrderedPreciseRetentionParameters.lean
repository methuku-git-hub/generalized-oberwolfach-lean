module

public import Oberwolfach.FirstVortexPreparedOrderedPreciseParameters
public import Oberwolfach.FirstVortexOrderedAllHubRetention

@[expose] public section
/-! A single choice in the original order supplies both all-hub retention
and the precise matching and first-active edit budgets. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
local instance orderedPreciseRetentionDecEq {V:Type}:DecidableEq V:=orderedRetentionDecEq

theorem first_vortex_ordered_precise_retention_parameters
    (a α C₀ εupper:ℝ) (m:ℕ) (ha:0<a) (hα:0<α) (hC:0<C₀) (hupper:0<εupper) (hm:0<m):
    ∃ε:ℝ,0<ε ∧ ε≤εupper ∧ ε≤1/4 ∧ ε≤a/8192 ∧ ε≤α/(1000*C₀) ∧
    ∀cap θupper:ℝ,0<cap→0<θupper→
    ∃θmax:ℝ,0<θmax ∧ θmax≤θupper ∧ θmax≤1/100 ∧ ∀θ:ℝ,0<θ→θ≤θmax→∀dmin:ℕ,
    ∃d:ℕ,dmin≤d ∧ 3≤d ∧ 1/(d:ℝ)≤θ/1024 ∧
    ∃ζglobal ζlocal:ℝ,0<ζglobal ∧ 0<ζlocal ∧ ζglobal≤θ/4096 ∧ ζlocal≤cap/128 ∧
      (∃Nret:ℕ,∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/((m:ℝ)+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζglobal*n)+errOrd≤4*θ*n) ∧
      (∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
       ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
       RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J→
       RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J) ∧
    ∀upper:ℝ,0<upper→
    ∃lamBase lamAssign ξCap:ℝ,
      0<lamBase ∧ 0<lamAssign ∧ lamBase≤lamAssign ∧ lamAssign≤upper ∧
      lamAssign≤1 ∧ lamAssign≤θ ∧ lamAssign≤α/128 ∧ lamAssign≤cap*a/4096 ∧ 0<ξCap ∧
      (∀ξ:ℝ,ξ≤ξCap→lamBase+ξ≤a*θ/4096 ∧ ξ/2≤(lamAssign-lamBase)*ε) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(a' γ:ℝ),max a' γ≤1/(10*(d:ℝ))→
        2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a' γ*n≤cap*(ε*n)/128 ∧
        ∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
          2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  obtain ⟨ε,hε,hεupper,hεquarter,hεa,hεα,hChoice⟩:=
    first_vortex_prepared_ordered_precise_parameters a α C₀ εupper ha hα hC hupper
  refine ⟨ε,hε,hεupper,hεquarter,hεa,hεα,?_⟩
  intro cap θupper hcap hθupper
  obtain ⟨θmax,hθmax,hθupper',hθsmall,hθ⟩:=hChoice cap θupper hcap hθupper
  refine ⟨θmax,hθmax,hθupper',hθsmall,?_⟩
  intro θ hθ0 hθmax' dmin
  obtain ⟨d,hdmin,hd,hspacing,hrates⟩:=hθ θ hθ0 hθmax' dmin
  obtain ⟨ζglobal,ζlocal,hζglobal,hζlocal,hζθ,hζcap,hNret,hRet⟩:=
    first_vortex_ordered_all_hub_retention ε cap θ m d hε (by linarith) hcap hθ0 hm (by omega) hspacing
  exact ⟨d,hdmin,hd,hspacing,ζglobal,ζlocal,hζglobal,hζlocal,hζθ,hζcap,hNret,hRet,hrates⟩
end Oberwolfach
