module

public import Oberwolfach.OrdinaryBoundarySmallDensityChoice

@[expose] public section
/-! The root-cover, packing, cleanup and fresh-density rates can be chosen
    in order below any earlier positive caps and protected-trace budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_trace_rates (κ ζ rate pcap othercap:ℝ)
    (hκ:0<κ) (hζ:0<ζ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃p εsup τ ν η ell:ℝ,
      0<p ∧ p≤1 ∧ p≤pcap ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧
      0<τ ∧ 0<ν ∧ 0<η ∧ 0<ell ∧ τ≤othercap ∧ ν≤othercap ∧ η≤othercap ∧ ell≤othercap ∧
      τ+ν≤p^2/4 ∧ τ+ν+ell≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4 ∧ ν+η+4*p≤rate ∧
    ∃N:ℕ,∀n:ℕ,N≤n→2≤ζ*κ*p*n/4 :=by
  let cap:=min pcap (rate/16)
  have hcap:0<cap:=lt_min hpcap (by positivity)
  obtain ⟨p,hp,hp1,hpc,hpκ,hsqrt⟩:=ordinary_boundary_small_density_choice κ ζ cap hκ hζ hcap
  have hpcap':p≤pcap:=hpc.trans (min_le_left _ _)
  have hprate:p≤rate/16:=hpc.trans (min_le_right _ _)
  let a:ℝ:=min (p^2/32) (min (ζ*κ*p/32) (min (rate/16) (othercap/2)))
  let εsup:ℝ:=p^2/8
  have ha:0<a:=by dsimp [a];positivity
  have hap:a≤p^2/32:=min_le_left _ _
  have hak:a≤ζ*κ*p/32:=(min_le_right _ _).trans (min_le_left _ _)
  have har:a≤rate/16:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hac:a≤othercap/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have he:0<εsup:=by dsimp [εsup];positivity
  have hecap:εsup≤p^2/4:=by dsimp [εsup];nlinarith [sq_nonneg p]
  have haother:a≤othercap:=by linarith
  have hsum:a+a≤p^2/4:=by nlinarith [sq_nonneg p]
  have hclass:a+a+a≤ζ*κ*p/4:=by nlinarith [mul_pos (mul_pos hζ hκ) hp]
  have hδ:a+a≤ζ*κ*p/4:=by nlinarith [mul_pos (mul_pos hζ hκ) hp]
  have hcost:a+a+4*p≤rate:=by linarith
  obtain ⟨N,hN⟩:=exists_nat_ge (8/(ζ*κ*p))
  refine ⟨p,εsup,a,a,a,a,hp,hp1,hpcap',hpκ,hsqrt,he,hecap,ha,ha,ha,ha,haother,haother,haother,haother,hsum,hclass,hδ,hcost,N,?_⟩
  intro n hn
  have hnreal:(N:ℝ)≤n:=by exact_mod_cast hn
  have hden:0<ζ*κ*p:=mul_pos (mul_pos hζ hκ) hp
  have hmul:8≤(n:ℝ)*(ζ*κ*p):=(div_le_iff₀ hden).mp (hN.trans hnreal)
  nlinarith only [hmul]
end Oberwolfach
