module

public import Oberwolfach.OrdinaryBoundaryRowSumBound

@[expose] public section
/-! A linear capacity choice and sparse host/conflict degrees imply the
quantitative extension budget needed for the general boundary completion. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_completion_budget
    (m n ns D K:ℕ) (ρ φ δ k ν β slack:ℝ)
    (hn:0<n) (hk:0<k) (hK:0<K) (hφ:0≤φ) (hδ:0≤δ)
    (hns:ns≤n*D) (hD:(D:ℝ)≤δ*n) (hKlow:k*n≤(K:ℝ)) (hKhigh:(K:ℝ)≤k*n+1)
    (Lconf t:ℝ) (hLconf:Lconf≤φ*n) (ht:t≤ν*n)
    (hsize:((m:ℝ)+8)≤slack*n)
    (hmargin:((m:ℝ)+1)*δ/k+((m:ℝ)+4)*φ+4*ρ+4*k+((m:ℝ)+9)*δ+3*ν+slack<β):
    ((ns*(m+1):ℕ):ℝ)/(K:ℝ)+(((m+1:ℕ):ℝ)+3)*(Lconf+1)+
      2*(2*(ρ*n)+2*((K+D:ℕ):ℝ))+(D:ℝ)+((D*(m+1):ℕ):ℝ)+3*D < β*n-3*t:=by
  have hn0:(0:ℝ)<n:=by exact_mod_cast hn
  have hK0:(0:ℝ)<K:=by exact_mod_cast hK
  have hnsr:(ns:ℝ)≤(n:ℝ)*D:=by exact_mod_cast hns
  have hden:(k*(n:ℝ))≤K:=hKlow
  have hratio:(ns:ℝ)/(K:ℝ)≤(δ/k)*n:=by
    apply (div_le_iff₀ hK0).2
    have hprod:(ns:ℝ)≤δ*(n:ℝ)*(n:ℝ):=by nlinarith [hnsr,hD]
    have hfac:0≤δ/k:=div_nonneg hδ hk.le
    have hfn:0≤(δ/k)*(n:ℝ):=mul_nonneg hfac hn0.le
    have hmult:=mul_le_mul_of_nonneg_left hden hfn
    have heq:(δ/k)*(n:ℝ)*(k*n)=δ*n*n:=by field_simp
    rw [heq] at hmult
    nlinarith [hprod,hmult]
  have hm0:0≤(m:ℝ)+1:=by positivity
  have hratio2:=mul_le_mul_of_nonneg_left hratio hm0
  have hratio3:(ns:ℝ)*((m:ℝ)+1)/K≤(((m:ℝ)+1)*δ/k)*n:=by
    convert hratio2 using 1 <;> ring
  have hDcoef:=mul_le_mul_of_nonneg_left hD (show 0≤(m:ℝ)+9 by positivity)
  have hLcoef:=mul_le_mul_of_nonneg_left hLconf (show 0≤(m:ℝ)+4 by positivity)
  have hconst:=mul_lt_mul_of_pos_right hmargin hn0
  have hbound:(ns:ℝ)*((m:ℝ)+1)/K+((m:ℝ)+4)*(Lconf+1)+
      2*(2*(ρ*n)+2*((K:ℝ)+D))+(D:ℝ)+(D:ℝ)*((m:ℝ)+1)+3*D ≤
      (((m:ℝ)+1)*δ/k+((m:ℝ)+4)*φ+4*ρ+4*k+((m:ℝ)+9)*δ)*n+((m:ℝ)+8):=by
    nlinarith only [hratio3,hDcoef,hLcoef,hKhigh]
  push_cast
  nlinarith only [hbound,hconst,hsize,ht]
end Oberwolfach
