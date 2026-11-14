module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
/-! Reserved lists are disjoint from retained marked vertices, so their
extension margins do not require a cycle-length lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_continuation_capped_final
    (γ pstar βFinalCap:ℝ) (hγ:0<γ) (hp:0<pstar) (hCap:0<βFinalCap):
    ∃β lamList ζList βfinal δ:ℝ,
      0<β ∧ β≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧ βfinal≤βFinalCap ∧ 0<δ ∧ δ≤(βfinal/100)^2 ∧ δ≤1/100 ∧
      (∀εQ:ℝ,εQ≤lamList/2→βfinal+εQ≤lamList) ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤β*n:=by
  obtain ⟨β,lamList,ζList,hβ,hβ1,hlam,hlam1,hζ,dMin,hList⟩:=
    long_selected_list_margins (1/100) γ pstar (by norm_num) hγ hp
  let βfinal:=min (lamList/4) βFinalCap
  let δ:=min ((βfinal/100)^2) (1/100:ℝ)
  have hβfinal:0<βfinal:=by dsimp [βfinal]; positivity
  have hδ:0<δ:=by dsimp [δ]; positivity
  refine ⟨β,lamList,ζList,βfinal,δ,hβ,hβ1,hlam,hlam1,hζ,hβfinal,min_le_left _ _,?_,min_le_right _ _,hδ,min_le_left _ _,min_le_right _ _,?_,dMin,?_⟩
  · have hh:βfinal≤lamList/4:=min_le_left _ _; linarith
  · intro εQ hεQ; have hh:βfinal≤lamList/4:=min_le_left _ _; linarith
  · intro d hd hd2
    obtain ⟨N,hN⟩:=hList d hd hd2
    refine ⟨N,?_⟩
    intro n hn
    obtain ⟨herror,hmargin,hbudget⟩:=hN n hn
    refine ⟨herror,hmargin,?_⟩
    have hpos:(0:ℝ)≤(n:ℝ)/(8*(d:ℝ)):=by positivity
    have hpos2:(0:ℝ)≤2*(n:ℝ)^(3/4:ℝ)/d:=by positivity
    linarith
end Oberwolfach
