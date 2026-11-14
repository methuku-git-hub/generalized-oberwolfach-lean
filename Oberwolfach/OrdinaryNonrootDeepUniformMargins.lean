module

public import Oberwolfach.OrdinarySampleProfileNonrootBothCuts

@[expose] public section
/-! Uniform choices for the inner-set, blocker and edit-budget hypotheses
of the nonroot deep-cover theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_deep_uniform_margins
    (a ρ θ aLoad ζlimit:ℝ) (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (haLoad:0<aLoad) (hζ:0<ζlimit):
    ∃ε₀:ℝ,0<ε₀ ∧ ε₀≤1 ∧
    ∀ε:ℝ,0≤ε→ε≤ε₀→∀Dcut:ℕ,∃N:ℕ,1≤N ∧
    ∀n I T B W Ledit:ℝ,(N:ℝ)≤n→0≤I→I≤ε*n→0≤T→T≤ε*I→
      0≤B→B≤I→0≤W→W≤ε*B→0≤Ledit→Ledit≤ζlimit*I→
    let Lbase:=ζlimit*I;let L:=ρ*n/2;
      I≤a*n ∧ T≤θ*n ∧ 2*W≤L ∧ 0≤L ∧ L≤ρ*n ∧ (Dcut:ℝ)≤L ∧
      Ledit≤Lbase ∧ Lbase+I≤L ∧ Lbase+B≤L ∧ 4≤aLoad^2*n := by
  let ε₀:ℝ:=min 1 (min a (min θ (ρ/(4*(ζlimit+2)))))
  have hden:0<4*(ζlimit+2):=by positivity
  have he₀:0<ε₀:=lt_min (by norm_num) (lt_min ha (lt_min hθ (div_pos hρ hden)))
  have he₀one:ε₀≤1:=min_le_left _ _
  have he₀a:ε₀≤a:=(min_le_right _ _).trans (min_le_left _ _)
  have he₀θ:ε₀≤θ:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have he₀ρ:ε₀≤ρ/(4*(ζlimit+2)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε₀,he₀,he₀one,?_⟩
  intro ε hε hε₀ Dcut
  obtain ⟨N1,hN1⟩:=exists_nat_gt (2*(Dcut:ℝ)/ρ)
  obtain ⟨N2,hN2⟩:=exists_nat_gt (4/aLoad^2)
  let N:=max (max N1 N2) 1
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro n I T B W Ledit hn hI0 hI hT0 hT hB0 hB hW0 hW hL0 hL Lbase L
  have hn0:0≤n:=le_trans (by positivity) hn
  have hN1n:(N1:ℝ)≤n:=by
    have hh:(N1:ℝ)≤N:=by exact_mod_cast (show N1≤N by dsimp [N];omega)
    exact hh.trans hn
  have hN2n:(N2:ℝ)≤n:=by
    have hh:(N2:ℝ)≤N:=by exact_mod_cast (show N2≤N by dsimp [N];omega)
    exact hh.trans hn
  have hεone:ε≤1:=hε₀.trans he₀one
  have hεa:ε≤a:=hε₀.trans he₀a
  have hεθ:ε≤θ:=hε₀.trans he₀θ
  have hεbudget:ε*(ζlimit+2)≤ρ/4:=by
    have hh:= (le_div_iff₀ hden).mp (hε₀.trans he₀ρ)
    nlinarith only [hh]
  have hIn:I≤n:=by
    have hh:=mul_le_mul_of_nonneg_right hεone hn0
    nlinarith only [hI,hh]
  have hIa:I≤a*n:=hI.trans (mul_le_mul_of_nonneg_right hεa hn0)
  have hTθ:T≤θ*n:=by
    have hh:=mul_le_mul_of_nonneg_left hIn hε
    have hh':=mul_le_mul_of_nonneg_right hεθ hn0
    nlinarith only [hT,hh,hh']
  have hscale:(ζlimit+2)*I≤(ρ/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_left hI (show 0≤ζlimit+2 by linarith)
    have hh':=mul_le_mul_of_nonneg_right hεbudget hn0
    nlinarith only [hh,hh']
  have hW:2*W≤L:=by
    have hh:=mul_le_mul_of_nonneg_left hB hε
    have hh':=mul_le_mul_of_nonneg_left hIn hε
    have hεquarter:ε≤ρ/8:=by nlinarith [mul_nonneg hε hζ.le]
    have hh'':=mul_le_mul_of_nonneg_right hεquarter hn0
    dsimp [L]
    have hnon:=mul_nonneg hρ.le hn0
    nlinarith only [hW,hh,hh',hh'',hnon]
  have hLnonneg:0≤L:=by dsimp [L];positivity
  have hLupper:L≤ρ*n:=by dsimp [L];nlinarith [mul_nonneg hρ.le hn0]
  have hD:(Dcut:ℝ)≤L:=by
    have hh:2*(Dcut:ℝ)<(N1:ℝ)*ρ:=(div_lt_iff₀ hρ).mp hN1
    have hh':=(mul_le_mul_of_nonneg_right hN1n hρ.le)
    dsimp [L]
    nlinarith only [hh,hh']
  have hLI:Lbase+I≤L:=by
    dsimp [Lbase,L]
    have hp:=mul_nonneg hρ.le hn0
    nlinarith only [hscale,hI0,hζ,hp]
  have hLB:Lbase+B≤L:=by linarith
  have hload:4≤aLoad^2*n:=by
    have hp:0<aLoad^2:=sq_pos_of_pos haLoad
    have hh:4<(N2:ℝ)*aLoad^2:=(div_lt_iff₀ hp).mp hN2
    have hh':=mul_le_mul_of_nonneg_right hN2n hp.le
    nlinarith only [hh,hh']
  exact ⟨hIa,hTθ,hW,hLnonneg,hLupper,hD,hL,hLI,hLB,hload⟩
end Oberwolfach
