module

public import Oberwolfach.OrdinaryBoundaryCompletionTraceBudget
public import Oberwolfach.OrdinaryBoundaryCompletionHierarchyCappedExplicit
public import Oberwolfach.OrdinaryBoundaryCompletionBudget

@[expose] public section
/-! The linear endpoint capacity and the complete finishing load can be
chosen below any earlier positive protected-trace rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_completion_trace_budget_uniform_capacity_explicit (m:ℕ) (β rate:ℝ) (hβ:0<β) (hrate:0<rate):
    ∃k:ℝ,k=min (rate/(2*((m:ℝ)+10))) (min 1 (β/(100*((m:ℝ)+20)))) ∧ 0<k ∧ k≤1 ∧ ∀δ φ ρ ν:ℝ,
      0≤δ→0≤φ→0≤ρ→0≤ν→δ≤k^2→φ≤k^2→ρ≤k^2→ν≤k^2→∃N:ℕ,
    ∀n:ℕ,N≤n→∃K:ℕ,0<K ∧ (K:ℝ)≤k*n+1 ∧
    ∀(D:ℕ) (Lconf t:ℝ),
      (D:ℝ)≤δ*n→Lconf≤φ*n→t≤ν*n→
      ((n*D*(m+1):ℕ):ℝ)/(K:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*n)+2*((K+D:ℕ):ℝ))+
      (D:ℝ)+((D*(m+1):ℕ):ℝ)+3*D < β*n-3*t ∧
      ν*n+2*(ρ*n)+((3*(K+D)+D*(m+1):ℕ):ℝ)≤rate*n :=by
  let cap:ℝ:=rate/(2*((m:ℝ)+10))
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨k,hkeq,hk,hk1,hkcap,hmargin⟩:=ordinary_boundary_completion_hierarchy_capped_explicit m β cap hβ hcap
  have hk2:k^2≤k:=by nlinarith
  have hcoef:3*k+((m:ℝ)+7)*k^2≤rate/2:=by
    have hm:0≤(m:ℝ)+7:=by positivity
    have hh:=mul_le_mul_of_nonneg_left hk2 hm
    have hr:(2*((m:ℝ)+10))*k≤rate:=by
      have hh':k≤rate/(2*((m:ℝ)+10)):=by simpa only [cap] using hkcap
      have hh'':k*(2*((m:ℝ)+10))≤rate:=(le_div_iff₀ (by positivity)).mp hh'
      nlinarith only [hh'']
    nlinarith only [hh,hr]
  refine ⟨k,by simpa only [cap] using hkeq,hk,hk1,?_⟩
  intro δ φ ρ ν hδ hφ hρ hν hδk hφk hρk hνk
  let N:=max (max 1 ⌈((m:ℝ)+8)/k^2⌉₊) ⌈6/rate⌉₊
  refine ⟨N,?_⟩
  intro n hn
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hnreal:(0:ℝ)<n:=by exact_mod_cast hn0
  have hk2pos:0<k^2:=sq_pos_of_pos hk
  have hN:((m:ℝ)+8)/k^2≤(n:ℝ):=by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈((m:ℝ)+8)/k^2⌉₊≤n by dsimp [N] at hn;omega))
  have hsize:((m:ℝ)+8)≤k^2*n:=by
    have hh:((m:ℝ)+8)≤(n:ℝ)*k^2:=(div_le_iff₀ hk2pos).mp hN
    nlinarith only [hh]
  have hNrate:6/rate≤(n:ℝ):=by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈6/rate⌉₊≤n by dsimp [N] at hn;omega))
  have hthree:3≤rate*n/2:=by
    have hh:6≤(n:ℝ)*rate:=(div_le_iff₀ hrate).mp hNrate
    nlinarith only [hh]
  let K:=⌈k*(n:ℝ)⌉₊
  have hKlow:k*(n:ℝ)≤(K:ℝ):=Nat.le_ceil _
  have hKhigh:(K:ℝ)≤k*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤k*(n:ℝ))).le
  have hK:0<K:=by
    have hh:0<(K:ℝ):=lt_of_lt_of_le (mul_pos hk hnreal) hKlow
    exact_mod_cast hh
  refine ⟨K,hK,hKhigh,?_⟩
  intro D Lconf t hD hL ht
  have hineq:=ordinary_boundary_completion_budget m n
    (n*D) D K ρ φ δ k ν β (k^2) hn0 hk hK hφ hδ le_rfl hD hKlow hKhigh Lconf t hL ht hsize
    (hmargin δ φ ρ ν (k^2) hδ hδk hφk hρk hνk le_rfl)
  refine ⟨hineq,?_⟩
  have hDk:(D:ℝ)≤k^2*n:=hD.trans (mul_le_mul_of_nonneg_right hδk hnreal.le)
  have hρn:ρ*n≤k^2*n:=mul_le_mul_of_nonneg_right hρk hnreal.le
  have hνn:ν*n≤k^2*n:=mul_le_mul_of_nonneg_right hνk hnreal.le
  have hDm:=mul_le_mul_of_nonneg_left hDk (show (0:ℝ)≤(m:ℝ)+4 by positivity)
  have hKthree:=mul_le_mul_of_nonneg_left hKhigh (show (0:ℝ)≤3 by norm_num)
  have hcoefn:=mul_le_mul_of_nonneg_right hcoef hnreal.le
  push_cast
  nlinarith only [hDm,hKthree,hρn,hνn,hcoefn,hthree]
end Oberwolfach
