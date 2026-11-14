module

public import Oberwolfach.OrdinaryPlacementOriginalSpacingRates

@[expose] public section
/-! The current coarse extending-list budget cannot be instantiated with the
small reserved sampling density and the abundance spacing. This identifies an
obstruction in the proof route, not a counterexample to the main theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_list_budget_scalar_obstruction
    (d K:ℝ) (hd:0<d) (hK:1≤K) (hdK:d≤K)
    (θ γ pstar βList:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hγ:0≤γ) (hγ1:γ≤1)
    (hp:0≤pstar) (hpK:pstar≤1/(4*K))
    (hbudget:1/d≤βList) (hmargin:βList≤γ*pstar^2*(θ/2)):False:=by
  have hK0:0<K:=by linarith
  have hpk:1/(4*K)≤1:=by
    apply (div_le_iff₀ (by positivity : 0<4*K)).2
    nlinarith
  have hp1:pstar≤1:=hpK.trans hpk
  have hsq0:0≤pstar^2:=sq_nonneg _
  have hsq:pstar^2≤pstar:=by nlinarith
  have hγsq:γ*pstar^2≤pstar^2:=by nlinarith
  have hγsq0:0≤γ*pstar^2:=mul_nonneg hγ hsq0
  have hθsq:(γ*pstar^2)*θ≤γ*pstar^2:=by nlinarith
  have hupper:βList≤pstar/2:=by nlinarith [hmargin,hγsq,hθsq,hsq]
  have hinv:1/K≤1/d:=(one_div_le_one_div_of_le hd hdK)
  have hsmall:pstar/2≤1/(8*K):=by
    have heq:1/(8*K)=(1/(4*K))/2:=by ring
    rw [heq]
    linarith
  have hlarge:1/(8*K)<1/K:=by
    have hpos:0<1/K:=by positivity
    have heq:1/(8*K)=(1/K)/8:=by ring
    rw [heq]
    linarith
  linarith

theorem ordinary_abundance_spacing_coarse_list_obstruction
    (d K m n:ℝ) (hd:0<d) (hK:1≤K) (hm:0≤m) (hn:0<n)
    (θ γ ρ rsv pstar βList lamList ζDel err:ℝ)
    (hθ:0<θ) (hθ1:θ≤1) (hγ:0≤γ) (hγ1:γ≤1)
    (hρ:0≤ρ) (hρ1:ρ≤1) (hrsv:0≤rsv) (hrsvK:rsv≤1/(2*K))
    (hpstar:0≤pstar) (hp:pstar≤ρ*rsv/2)
    (hlam:0≤lamList) (hζ:0≤ζDel) (herr:0≤err)
    (hcut:5/((m+1)*d+5)+(m+1)*d/K≤θ/2)
    (hbudget:(lamList+2*ζDel)*n+(n+2*err)/d≤βList*n)
    (hmargin:βList*n+err≤(γ*pstar^2)*n*(θ/2)):False:=by
  have hK0:0<K:=by linarith
  have hden:0<(m+1)*d+5:=by positivity
  have hfirst:0≤5/((m+1)*d+5):=by positivity
  have hratio:(m+1)*d/K≤θ/2:=by linarith
  have hprod:(m+1)*d≤(θ/2)*K:=(div_le_iff₀ hK0).mp hratio
  have hmd:0≤m*d:=mul_nonneg hm hd.le
  have hθK:θ*K≤K:=by nlinarith
  have hdK:d≤K:=by nlinarith
  have hrsvρ:ρ*rsv≤rsv:=by nlinarith
  have hpbound:pstar≤1/(4*K):=by
    have heq:(1/(2*K))/2=1/(4*K):=by ring
    rw [←heq]
    linarith
  have hnfrac:n/d≤(n+2*err)/d:=div_le_div_of_nonneg_right (by linarith) hd.le
  have hln:0≤(lamList+2*ζDel)*n:=mul_nonneg (by linarith) hn.le
  have hmul:(1/d)*n≤βList*n:=by
    have heq:(1/d)*n=n/d:=by ring
    rw [heq]
    linarith
  have hbudget':1/d≤βList:=(mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using hmul)
  have hmul':βList*n≤(γ*pstar^2*(θ/2))*n:=by nlinarith [hmargin]
  have hmargin':βList≤γ*pstar^2*(θ/2):=(mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using hmul')
  exact ordinary_list_budget_scalar_obstruction d K hd hK hdK θ γ pstar βList hθ.le hθ1 hγ hγ1 hpstar hpbound hbudget' hmargin'
end Oberwolfach
