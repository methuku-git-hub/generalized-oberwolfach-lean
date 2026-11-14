module

public import Oberwolfach.LongReservedContinuationNoMarkedLoss
public import Oberwolfach.FirstVortexNoMarkedParameterChoices

@[expose] public section
/-! The list and matching tolerances coexist with the original order of
choices and require no cycle-length lower bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_no_marked_joint_choices
    (γList pstar b ρ₀ θ δold C₀:ℝ)
    (hγ:0<γList) (hp:0<pstar) (hb:0<b) (hρ:0<ρ₀) (hθ:0<θ)
    (hδold:0<δold) (hC:1≤C₀):
    ∃βlist lamList ζList βfinal δglobal αMatch εQ lam lamAssign:ℝ,
      0<βlist ∧ βlist≤1 ∧ 0<lamList ∧ lamList≤1/100 ∧ 0<ζList ∧
      0<βfinal ∧ βfinal≤lamList/4 ∧ βfinal≤1 ∧ 0<δglobal ∧ δglobal≤(βfinal/100)^2 ∧ δglobal≤1/100 ∧
      0<αMatch ∧ (2*αMatch)/16≤b ∧
      (2*αMatch)/16≤((ρ₀/4)/40000)*θ/1024 ∧ 2*αMatch≤4*δglobal ∧
      0<εQ ∧ εQ≤δglobal ∧ βfinal+εQ≤lamList ∧
      εQ≤αMatch/(1000*C₀) ∧ εQ≤(ρ₀/4)/80000 ∧
      0<lam ∧ lam≤θ ∧ lam≤αMatch/128 ∧ lam≤δold*εQ/32 ∧ lam<lamAssign ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→2≤d→∃N:ℕ,∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
      βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤βlist*n :=by
  obtain ⟨βlist,lamList,ζList,βfinal,δglobal,hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,htrim,dMin,hList⟩:=
    long_reserved_continuation_no_marked_loss γList pstar hγ hp
  obtain ⟨αMatch,εQ,lam,lamAssign,hα,hαb,hαsmall,hαglobal,hε,hεδ,hlist,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign⟩:=
    first_vortex_no_marked_parameter_choices b ρ₀ θ δold δglobal lamList βfinal C₀ hb hρ hθ hδold hδglobal hlamList hβfinal.le hβbound hC
  exact ⟨βlist,lamList,ζList,βfinal,δglobal,αMatch,εQ,lam,lamAssign,
    hβ,hβ1,hlamList,hlamList1,hζ,hβfinal,hβbound,hβfinal1,hδglobal,hδbound,hδ1,
    hα,hαb,hαsmall,hαglobal,hε,hεδ,hlist,hεα,hερ,hlam,hlamθ,hlamα,hlamδ,hlamAssign,dMin,hList⟩
end Oberwolfach
