module

public import Oberwolfach.PairHubDensityBounds

@[expose] public section
/-! Choose the row and load error margins before the graph size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_sampled_profile_margins_fixed_beta (r:ℕ) (α pmin smin η b L:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hη:0<η) (hb:0≤b) (hL:0≤L):
    let β:=α*pmin^2*smin^2;
    0<β ∧ ∃ rowErr t ε:ℝ,0<rowErr∧0<t∧0<ε ∧
    ∃ N:ℕ,∀ n:ℕ,(N:ℝ)≤n → ∀ D:ℝ,(n:ℝ)/2≤D →
      β*n≤(pmin^2*smin^2)*(2*α)*n-rowErr*n-2*L ∧
      t/(pmin^r*(smin*smin)^(r-1))+(6*(r:ℝ)^4*b*L+ε*n)/D≤η := by
  intro β
  let cmin:=pmin^r*(smin*smin)^(r-1)
  let rowErr:=β/4
  let t:=η*cmin/4
  let ε:=η/8
  have hc:0<cmin:=by dsimp [cmin];positivity
  have hβ:0<β:=by dsimp [β];positivity
  have hrow:0<rowErr:=by dsimp [rowErr];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (4*L/β+48*(r:ℝ)^4*b*L/η+1)
  refine ⟨hβ,rowErr,t,ε,hrow,ht,hε,N,?_⟩
  intro n hn D hD
  have hterm1:0≤4*L/β:=by positivity
  have hterm2:0≤48*(r:ℝ)^4*b*L/η:=by positivity
  have hnreal:(0:ℝ)<n:=by nlinarith [hN,hn]
  have hDpos:0<D:=by linarith
  have hβn:4*L≤β*n:=by
    have hh:4*L/β≤(n:ℝ):=by linarith [hN,hn,hterm2]
    simpa only [mul_comm] using (div_le_iff₀ hβ).mp hh
  have hconf:48*(r:ℝ)^4*b*L≤η*n:=by
    have hh:48*(r:ℝ)^4*b*L/η≤(n:ℝ):=by linarith [hN,hn,hterm1]
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hh
  constructor
  · dsimp [rowErr,β]
    dsimp [β] at hβn
    nlinarith only [hβn,hL]
  · have hfrac:(n:ℝ)/D≤2:=(div_le_iff₀ hDpos).mpr (by linarith)
    have hconfD:6*(r:ℝ)^4*b*L/D≤η/4:=by
      apply (div_le_iff₀ hDpos).mpr
      have hh:0≤η*(2*D-n):=mul_nonneg hη.le (by linarith)
      nlinarith only [hconf,hh]
    have herr:(ε*n)/D≤η/4:=by
      dsimp [ε]
      have hh:=mul_le_mul_of_nonneg_left hfrac (show 0≤η/8 by positivity)
      have heq:(η/8*n)/D=(η/8)*(n/D):=by ring
      rw [heq]
      calc
        _ ≤ (η/8)*2 := hh
        _ = η/4 := by ring
    have htdiv:t/cmin=η/4:=by dsimp [t];field_simp
    change t/cmin+(6*(r:ℝ)^4*b*L+ε*n)/D≤η
    rw [add_div,htdiv]
    linarith only [hconfD,herr,hη]
end Oberwolfach
