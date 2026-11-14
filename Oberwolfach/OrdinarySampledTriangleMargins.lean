module

public import Oberwolfach.PairHubDensityBounds

@[expose] public section
/-! Choose the row and load error margins before the graph size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_sampled_triangle_margins (α pmin smin η b L:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hη:0<η) (hb:0≤b) (hL:0≤L):
    ∃ β rowErr t ε:ℝ,0<β∧0<rowErr∧0<t∧0<ε ∧
    ∃ N:ℕ,∀ n:ℕ,(N:ℝ)≤n → ∀ D:ℝ,(n:ℝ)/2≤D →
      β*n≤(pmin^4*smin^4)*(4*(min α (1/4)))*n-rowErr*n-4*L ∧
      t/(pmin^3*(smin*smin)^2)+(6*(3:ℝ)^4*b*L+ε*n)/D≤η := by
  let cmin:=pmin^3*(smin*smin)^2
  let β:=2*(min α (1/4))*pmin^4*smin^4
  let rowErr:=β/4
  let t:=η*cmin/4
  let ε:=η/8
  have hc:0<cmin:=by dsimp [cmin];positivity
  have hβ:0<β:=by
    have hx:0<min α (1/4:ℝ):=lt_min hα (by norm_num)
    dsimp [β];positivity
  have hrow:0<rowErr:=by dsimp [rowErr];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨N,hN⟩:=exists_nat_gt (8*L/β+48*(3:ℝ)^4*b*L/η+1)
  refine ⟨β,rowErr,t,ε,hβ,hrow,ht,hε,N,?_⟩
  intro n hn D hD
  have hterm1:0≤8*L/β:=by positivity
  have hterm2:0≤48*(3:ℝ)^4*b*L/η:=by positivity
  have hnreal:(0:ℝ)<n:=by nlinarith [hN,hn]
  have hDpos:0<D:=by linarith
  have hβn:8*L≤β*n:=by
    have hh:8*L/β≤(n:ℝ):=by linarith [hN,hn,hterm2]
    simpa only [mul_comm] using (div_le_iff₀ hβ).mp hh
  have hconf:48*(3:ℝ)^4*b*L≤η*n:=by
    have hh:48*(3:ℝ)^4*b*L/η≤(n:ℝ):=by linarith [hN,hn,hterm1]
    simpa only [mul_comm] using (div_le_iff₀ hη).mp hh
  constructor
  · dsimp [rowErr,β]
    dsimp [β] at hβn
    nlinarith only [hβn,hL]
  · have hfrac:(n:ℝ)/D≤2:=(div_le_iff₀ hDpos).mpr (by linarith)
    have hconfD:6*(3:ℝ)^4*b*L/D≤η/4:=by
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
    change t/cmin+(6*(3:ℝ)^4*b*L+ε*n)/D≤η
    rw [add_div,htdiv]
    linarith only [hconfD,herr,hη]
end Oberwolfach
