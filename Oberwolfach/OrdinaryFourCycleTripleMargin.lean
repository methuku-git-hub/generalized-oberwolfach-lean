module

public import Oberwolfach.OrdinaryFourCycleTripleNeighbourhood

@[expose] public section
/-! A positive slack and row tolerance for the four-cycle triple bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_four_cycle_triple_margin (α pmin smin ω L:ℝ)
    (hα:0<α) (hp:0<pmin) (hs:0<smin) (hω:0<ω) (hL:0≤L):
    let c:ℝ:=(pmin^3*smin^3)*(3*(min α (1/3)));
    ∃ β row:ℝ,0<β ∧ 0<row ∧ β≤c/4 ∧ row≤c/4 ∧
      β≤α*pmin^2*smin^2 ∧ β≤ω*smin^10/4 ∧ row≤smin^10/2 ∧
      ∃ N:ℕ,∀ n:ℕ,(N:ℝ)≤n → β*n≤c*n-row*n-3*L := by
  intro c
  have hx:0<min α (1/3:ℝ):=lt_min hα (by norm_num)
  have hc:0<c:=by dsimp [c];positivity
  let β:ℝ:=min (c/4) (min (α*pmin^2*smin^2) (ω*smin^10/4))
  let row:ℝ:=min (c/4) (smin^10/2)
  have hβ:0<β:=by
    dsimp [β]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hr:0<row:=by dsimp [row]; apply lt_min <;> positivity
  have hβc:β≤c/4:=min_le_left _ _
  have hβbase:β≤α*pmin^2*smin^2:=(min_le_right _ _).trans (min_le_left _ _)
  have hβhub:β≤ω*smin^10/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hrc:row≤c/4:=min_le_left _ _
  have hrhub:row≤smin^10/2:=min_le_right _ _
  obtain ⟨N,hN⟩:=exists_nat_gt (6*L/c+1)
  refine ⟨β,row,hβ,hr,hβc,hrc,hβbase,hβhub,hrhub,N,?_⟩
  intro n hn
  have hn0:0≤(n:ℝ):=by positivity
  have hnL:6*L≤c*n:=by
    have hh:6*L/c≤(n:ℝ):=by linarith
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hh
  have hβn:=mul_le_mul_of_nonneg_right hβc hn0
  have hrn:=mul_le_mul_of_nonneg_right hrc hn0
  nlinarith only [hnL,hβn,hrn]
end Oberwolfach
