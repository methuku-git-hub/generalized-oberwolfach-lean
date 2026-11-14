module

public import Oberwolfach.OrdinaryBoundaryCompletionHierarchy

@[expose] public section
/-! Once the physical host and cleanup scales are sufficiently small, a
linear capacity chosen before the graph is enough for the endpoint finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_completion_available (m:ℕ) (β:ℝ) (hβ:0<β):
    ∃k:ℝ,0<k ∧ ∀δ φ ρ ν:ℝ,
      0≤δ→0≤φ→δ≤k^2→φ≤k^2→ρ≤k^2→ν≤k^2→∃N:ℕ,
    ∀n:ℕ,N≤n→∀(D:ℕ) (Lconf t:ℝ),
      (D:ℝ)≤δ*n→Lconf≤φ*n→t≤ν*n→
    ∃K:ℕ,0<K ∧
      ((n*D*(m+1):ℕ):ℝ)/(K:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*n)+2*((K+D:ℕ):ℝ))+
      (D:ℝ)+((D*(m+1):ℕ):ℝ)+3*D < β*n-3*t:=by
  obtain ⟨k,hk,hk1,hmargin⟩:=ordinary_boundary_completion_hierarchy m β hβ
  refine ⟨k,hk,?_⟩
  intro δ φ ρ ν hδ hφ hδk hφk hρk hνk
  let N:=max 1 ⌈((m:ℝ)+8)/k^2⌉₊
  refine ⟨N,?_⟩
  intro n hn D Lconf t hD hL ht
  have hn0:0<n:=by dsimp [N] at hn;omega
  have hnreal:(0:ℝ)<n:=by exact_mod_cast hn0
  have hk2:0<k^2:=sq_pos_of_pos hk
  have hN:((m:ℝ)+8)/k^2≤(n:ℝ):=by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈((m:ℝ)+8)/k^2⌉₊≤n from (le_max_right _ _).trans hn))
  have hsize:((m:ℝ)+8)≤k^2*n:=by
    have hh:((m:ℝ)+8)≤(n:ℝ)*k^2:=(div_le_iff₀ hk2).mp hN
    nlinarith only [hh]
  let K:=⌈k*(n:ℝ)⌉₊
  have hKlow:k*(n:ℝ)≤(K:ℝ):=Nat.le_ceil _
  have hKhigh:(K:ℝ)≤k*n+1:=(Nat.ceil_lt_add_one (by positivity:0≤k*(n:ℝ))).le
  have hK:0<K:=by
    have hh:0<(K:ℝ):=lt_of_lt_of_le (mul_pos hk hnreal) hKlow
    exact_mod_cast hh
  have hineq:=ordinary_boundary_completion_budget m n
    (n*D) D K
    ρ φ δ k ν β (k^2) hn0 hk hK hφ hδ le_rfl hD hKlow hKhigh Lconf t hL ht hsize
    (hmargin δ φ ρ ν (k^2) hδ hδk hφk hρk hνk le_rfl)
  exact ⟨K,hK,hineq⟩
end Oberwolfach
