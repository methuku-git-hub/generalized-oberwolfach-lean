module

public import Oberwolfach.OrdinaryBoundarySmallDensityChoice

@[expose] public section
/-! First choose a density cap, then accept any positive density below it;
    choose support and four independent error caps only afterwards. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_rates_after_density (κ ζ rate pcap othercap:ℝ)
    (hκ:0<κ) (hζ:0<ζ) (hrate:0<rate) (hpcap:0<pcap) (hother:0<othercap):
    ∃pbound:ℝ,0<pbound ∧ pbound≤pcap ∧
    ∀p:ℝ,0<p→p≤pbound→
    ∃εsup cap:ℝ, p≤1 ∧ p≤4*ζ*κ ∧ 20*Real.sqrt (2*p)≤ζ*κ/2 ∧
      0<εsup ∧ εsup≤p^2/4 ∧ 0<cap ∧ cap≤othercap ∧
      (∀τ ν η ell:ℝ,0≤τ→0≤ν→0≤η→0≤ell→τ≤cap→ν≤cap→η≤cap→ell≤cap→
        τ+ν≤p^2/4 ∧ τ+ν+ell≤ζ*κ*p/4 ∧ ν+η≤ζ*κ*p/4 ∧ ν+η+4*p≤rate) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2≤ζ*κ*p*n/4 :=by
  let upper:=min pcap (rate/16)
  have hupper:0<upper:=lt_min hpcap (by positivity)
  obtain ⟨pbound,hpbound,hpbound1,hupperbound,hpκ,hsqrt⟩:=
    ordinary_boundary_small_density_choice κ ζ upper hκ hζ hupper
  refine ⟨pbound,hpbound,hupperbound.trans (min_le_left _ _),?_⟩
  intro p hp hpbound'
  have hp1:p≤1:=hpbound'.trans hpbound1
  have hpκ':p≤4*ζ*κ:=hpbound'.trans hpκ
  have hpRate:p≤rate/16:=hpbound'.trans (hupperbound.trans (min_le_right _ _))
  have hsqrt':20*Real.sqrt (2*p)≤ζ*κ/2:=by
    have hh:=Real.sqrt_le_sqrt (show 2*p≤2*pbound by linarith)
    linarith
  let cap:ℝ:=min (p^2/32) (min (ζ*κ*p/32) (min (rate/16) (othercap/2)))
  let εsup:ℝ:=p^2/8
  have hc:0<cap:=by dsimp [cap];positivity
  have hcp:cap≤p^2/32:=min_le_left _ _
  have hck:cap≤ζ*κ*p/32:=(min_le_right _ _).trans (min_le_left _ _)
  have hcr:cap≤rate/16:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hco:cap≤othercap/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsup:0<εsup:=by dsimp [εsup];positivity
  have hsupCap:εsup≤p^2/4:=by dsimp [εsup];nlinarith [sq_nonneg p]
  obtain ⟨N,hN⟩:=exists_nat_ge (8/(ζ*κ*p))
  refine ⟨εsup,cap,hp1,hpκ',hsqrt',hsup,hsupCap,hc,by linarith,?_,N,?_⟩
  · intro τ ν η ell _ _ _ _ hτ hν hη hell
    constructor
    · nlinarith [sq_nonneg p]
    constructor
    · nlinarith [mul_pos (mul_pos hζ hκ) hp]
    constructor
    · nlinarith [mul_pos (mul_pos hζ hκ) hp]
    · linarith
  · intro n hn
    have hnreal:(N:ℝ)≤n:=by exact_mod_cast hn
    have hden:0<ζ*κ*p:=mul_pos (mul_pos hζ hκ) hp
    have hmul:8≤(n:ℝ)*(ζ*κ*p):=(div_le_iff₀ hden).mp (hN.trans hnreal)
    nlinarith only [hmul]
end Oberwolfach
