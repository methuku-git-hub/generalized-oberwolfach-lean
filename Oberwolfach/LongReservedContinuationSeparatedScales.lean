module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_continuation_separated_scales
    (γ pstar:ℝ) (hγ:0<γ) (hp:0<pstar):
    ∃β lamList ζList βfinal δ:ℝ,
      0<β ∧ β≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ 0<δ ∧ δ≤(βfinal/100)^2 ∧ δ≤1/100 ∧
    ∃dMin L₀:ℕ,
      (∀m:ℕ,L₀≤m→4/(m:ℝ)≤δ/4 ∧ 1/(100*(m:ℝ))≤lamList/8) ∧
      (∀m:ℕ,L₀≤m→∀ε η:ℝ,ε≤lamList/8→η≤lamList/8→
        βfinal+ε+1/(100*(m:ℝ))+η≤lamList) ∧
      ∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ) ∧
        (lamList+2*ζList)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤β*n :=by
  obtain ⟨β,lamList,ζList,hβ,hβ1,hlam,hlam1,hζ,dMin,hList⟩:=long_selected_list_margins (1/100) γ pstar (by norm_num) hγ hp
  let βfinal:=lamList/4
  let δ:=min ((βfinal/100)^2) (1/100:ℝ)
  have hβfinal:0<βfinal:=by dsimp [βfinal];positivity
  have hδ:0<δ:=by dsimp [δ];positivity
  obtain ⟨L₁,hL₁⟩:=exists_nat_gt (16/δ)
  obtain ⟨L₂,hL₂⟩:=exists_nat_gt (8/(100*lamList))
  let L₀:=max L₁ L₂
  have hM:∀m:ℕ,L₀≤m→4/(m:ℝ)≤δ/4 ∧ 1/(100*(m:ℝ))≤lamList/8:=by
    intro m hm
    have hm1:(16/δ)<(m:ℝ):=lt_of_lt_of_le hL₁ (by exact_mod_cast (show L₁≤m by omega))
    have hm2:(8/(100*lamList))<(m:ℝ):=lt_of_lt_of_le hL₂ (by exact_mod_cast (show L₂≤m by omega))
    have hm0:0<(m:ℝ):=lt_trans (by positivity : 0<16/δ) hm1
    have hp1:16<δ*m:=by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hm1
    have hp2:8<(100*lamList)*m:=by simpa only [mul_comm] using (div_lt_iff₀ (by positivity : 0<100*lamList)).mp hm2
    constructor
    · apply (div_le_iff₀ hm0).2; nlinarith
    · apply (div_le_iff₀ (by positivity : 0<100*(m:ℝ))).2; nlinarith
  refine ⟨β,lamList,ζList,βfinal,δ,hβ,hβ1,hlam,hlam1,hζ,hβfinal,le_refl _,hδ,
    min_le_left _ _,min_le_right _ _,dMin,L₀,hM,?_,hList⟩
  intro m hm ε η hε hη
  have hh:=(hM m hm).2
  dsimp [βfinal]
  linarith
end Oberwolfach
