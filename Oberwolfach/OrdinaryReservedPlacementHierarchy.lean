module

public import Oberwolfach.OrdinaryReservedEarlyParameters
public import Oberwolfach.OrdinaryPlacementRatesBeforeSpacing

@[expose] public section
/-! Select the reserved-list, matching, assignment and physical-edit rates
in the order required by ordinary completion, before choosing spacing. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_placement_hierarchy
    (m:ℕ) (βfreq ρ₀ γ cap:ℝ) (hβfreq:0<βfreq) (hρ₀:0<ρ₀) (hγ:0<γ) (hcap:0<cap):
    ∃smin pstar β lam ζ δ θ α κ b z matchErr σ:ℝ,
      smin=βfreq/200 ∧ 0<smin ∧ pstar=(min 1 (ρ₀*smin))/2 ∧ 0<pstar ∧
      2*pstar≤1 ∧ 2*pstar≤ρ₀*smin ∧ 0<β ∧ β≤1 ∧ 0<lam ∧ 0<ζ ∧ lam+2*ζ≤β ∧
      0<δ ∧ δ≤((lam/2)/100)^2 ∧ 5*Real.sqrt δ≤cap ∧ 0<θ ∧ θ≤1/100 ∧ θ≤δ/8 ∧
      α=5*ρ₀*smin^2/128 ∧ 0<α ∧ 0<κ ∧ 0<b ∧ 0<z ∧ 0<matchErr ∧ 0<σ ∧
      b≤ζ ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→
        edit≤σ*n→inner≤σ*n→ reserve≤σ*n→conflict≤σ*n→
        edit+2*inner+reserve+conflict≤b*n) ∧
    ∀(d:ℕ),0<d→1/(4*(d:ℝ))≤5*θ^2/256→
      ∃ζret:ℝ,0<ζret ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*pstar^2*n*smin :=by
  obtain ⟨smin,pstar,β,lam,ζ,δ,θ,hsEq,hs,hpEq,hp,hp1,hpρ,hβ,hβ1,hlam,hζ,hbudget,
    hδ,hδsmall,hδcap,hθ,hθ1,hθδ,hN⟩:=ordinary_reserved_early_parameters βfreq ρ₀ γ cap hβfreq hρ₀ hγ hcap
  let α:ℝ:=5*ρ₀*smin^2/128
  have hα:0<α:=by dsimp [α];positivity
  obtain ⟨κ,b,z,matchErr,σ,hκ,hb,hz,hm,hσ,hbζ,hbα,hbδ,hzb,hphysical,hplace⟩:=
    ordinary_placement_rates_before_spacing m θ δ α ζ hθ hθ1 hδ hθδ hα hζ
  refine ⟨smin,pstar,β,lam,ζ,δ,θ,α,κ,b,z,matchErr,σ,hsEq,hs,hpEq,hp,hp1,hpρ,hβ,hβ1,hlam,hζ,hbudget,
    hδ,hδsmall,hδcap,hθ,hθ1,hθδ,rfl,hα,hκ,hb,hz,hm,hσ,hbζ,hbα,hbδ,hzb,hphysical,?_⟩
  intro d hd hspace
  obtain ⟨ζret,hζret,hcap',hsize,hmass⟩:=hplace d hd hspace
  obtain ⟨N,hN⟩:=hN d
  exact ⟨ζret,hζret,hcap',hsize,hmass,N,hN⟩
end Oberwolfach
