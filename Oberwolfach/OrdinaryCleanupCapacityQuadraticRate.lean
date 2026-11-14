module

public import Oberwolfach.OrdinaryCleanupCapacityRateConstraint

@[expose] public section
/-! The conflict-capacity term forces the fresh rate to be quadratic in the
boundary tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_capacity_quadratic_rate
    (N K D R p β:ℝ) (hN:0<N) (hK:0<K) (hR:0<R) (hp:0≤p)
    (hD:2*p*N≤D) (hcapacity:N*D*R/K+4*K<β*N/4):
    512*p*R<β^2 :=by
  have hD0:0≤D:=le_trans (by positivity) hD
  let A:ℝ:=N*D*R/K
  have hA:0≤A:=by dsimp [A];positivity
  have hAK:A*K=N*D*R:=by dsimp [A];field_simp
  have hsum:0<A+4*K:=by positivity
  have htarget:0<β*N/4:=lt_trans hsum hcapacity
  have hsq:(A+4*K)^2<(β*N/4)^2:=by
    have hh:=mul_pos (sub_pos.mpr hcapacity) (add_pos htarget hsum)
    nlinarith only [hh]
  have hAM:16*N*D*R≤(A+4*K)^2:=by
    have hh:=sq_nonneg (A-4*K)
    nlinarith only [hh,hAK]
  have hD':2*p*N*(N*R)≤D*(N*R):=by
    have hh:=mul_le_mul_of_nonneg_left hD (mul_nonneg hN.le hR.le)
    nlinarith only [hh]
  by_contra h
  have hbad:(β^2-512*p*R)*N^2≤0:=mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg N)
  nlinarith only [hsq,hAM,hD',hbad]
theorem ordinary_cleanup_capacity_rule_actual_quadratic_rate
    (N Kcap Dmax m:ℕ) (p βe ν Lconf:ℝ) (hN:0<N) (hK:0<Kcap)
    (hp:0≤p) (hν:0≤ν) (hL:0≤Lconf) (hD:(2*p)*N≤(Dmax:ℝ))
    (hcapacity:((N*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*N)+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*N-3*(ν*N)):
    512*p*((m:ℝ)+1)<βe^2 :=by
  have hN':(0:ℝ)<N:=by exact_mod_cast hN
  have hK':(0:ℝ)<Kcap:=by exact_mod_cast hK
  let extra:ℝ:=(((m+1:ℕ):ℝ)+3)*(Lconf+1)+8*p*N+4*(Dmax:ℝ)+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax+3*(ν*N)
  have hextra:0≤extra:=by dsimp [extra];positivity
  have hbound:(N:ℝ)*Dmax*((m:ℝ)+1)/(Kcap:ℝ)+4*(Kcap:ℝ)<βe*N/4:=by
    dsimp [extra] at hextra
    push_cast at hcapacity hextra
    nlinarith only [hcapacity,hextra]
  exact ordinary_cleanup_capacity_quadratic_rate N Kcap Dmax ((m:ℝ)+1) p βe hN' hK' (by positivity) hp hD hbound
end Oberwolfach
