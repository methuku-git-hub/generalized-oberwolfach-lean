module

public import Oberwolfach.OrdinaryReservedPlacementHierarchy
public import Oberwolfach.OrdinaryReservedMatchingLoadRate
public import Oberwolfach.OrdinaryMatchingMassRates
public import Oberwolfach.OrdinaryBoundaryLoadSpacing

@[expose] public section
/-! Choose the selected-list and residual-placement rates first, then the
spacing, then the matching rates and their common boundary-load budget. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_matching_placement_capped_hierarchy
    (m:ℕ) (βfreq ρ₀ γhost cap:ℝ) (hβfreq:0<βfreq) (hρ₀:0<ρ₀) (hγ:0<γhost) (hcap:0<cap):
    ∃smin pstar β lamList ζ δ θ α κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      smin=βfreq/200 ∧ 0<smin ∧ pstar=(min 1 (ρ₀*smin))/2 ∧ 0<pstar ∧
      2*pstar≤1 ∧ 2*pstar≤ρ₀*smin ∧ 0<β ∧ β≤1 ∧ 0<lamList ∧ 0<ζ ∧ lamList+2*ζ≤β ∧
      0<δ ∧ δ≤1 ∧ δ≤((lamList/2)/100)^2 ∧ 5*Real.sqrt δ≤cap ∧ 0<θ ∧ θ≤1/100 ∧ θ≤δ/8 ∧
      α=5*ρ₀*smin^2/128 ∧ 0<α ∧ 0<κ ∧ 0<b ∧ 0<z ∧ 0<matchErr ∧ 0<σ ∧ σ≤cap ∧
      b≤ζ ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧ 0<κ' ∧ κ'≤κ ∧ 2≤dNeed ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→
        edit≤σ*n→inner≤σ*n→ reserve≤σ*n→ conflict≤σ*n→
        edit+2*inner+reserve+conflict≤b*n) ∧
    ∀(d:ℕ),dNeed≤d→1/(4*(d:ℝ))≤5*θ^2/256→
      ∃ζret:ℝ,0<ζret ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2 ∧
      ∃N:ℕ,1≤N ∧ (∀n:ℕ,N≤n→
        4/(d:ℝ)≤δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/16 ∧
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γhost*pstar^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γhost*pstar^2*n*smin) ∧
    ∀K:ℕ,0<K→∃lam a γ:ℝ,0<lam ∧ lam≤1 ∧ 0<a ∧ 0<γ ∧
      lam≤θ/10 ∧ γ≤lam/10 ∧ a≤κ' ∧ γ≤κ' ∧
      a≤θ/(1600*(K:ℝ)*(K:ℝ)) ∧
      0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 ∧
      lam+γ*(1-θ+lam)≤matchErr ∧ lam+γ*(1-θ+lam)<θ ∧
      ∀n:ℕ,2*((max a γ)*n)≤δ*n/8 :=by
  obtain ⟨smin,pstar,β,lamList,ζ,δ,θ,α,κ,b,z,matchErr,σ,hsEq,hs,hpEq,hp,hp1,hpρ,
    hβ,hβ1,hlam,hζ,hbudget,hδ,hδsmall,hδcap,hθ,hθ1,hθδ,hαEq,hα,hκ,hb,hz,hmatchErr,hσ,
    hbζ,hbα,hbδ,hzb,hphysical,hplace⟩:=ordinary_reserved_placement_hierarchy m βfreq ρ₀ γhost cap hβfreq hρ₀ hγ hcap
  obtain ⟨κ',hκ',hκ'κ,hκ'δ,hload⟩:=ordinary_reserved_matching_load_rate δ κ hδ hκ
  obtain ⟨dNeed,Nbound,hdNeed,hNbound,hboundary⟩:=ordinary_boundary_load_spacing_and_order δ hδ
  have hlam1:lamList≤1:=by linarith
  have hf0:0≤(lamList/2)/100:=by positivity
  have hf1:(lamList/2)/100≤1:=by linarith
  have hfSq:((lamList/2)/100)^2≤1:=by
    nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hf1)]
  have hδ1:δ≤1:=hδsmall.trans hfSq
  let σcap:=min σ cap
  have hσcap:0<σcap:=lt_min hσ hcap
  have hσle:σcap≤cap:=min_le_right _ _
  have hphysical':∀(n edit inner reserve conflict:ℝ),0≤n→
      edit≤σcap*n→inner≤σcap*n→ reserve≤σcap*n→conflict≤σcap*n→
      edit+2*inner+reserve+conflict≤b*n:=by
    intro n edit inner reserve conflict hn he hi hr hf
    have hle:=mul_le_mul_of_nonneg_right (min_le_left σ cap) hn
    exact hphysical n edit inner reserve conflict hn (he.trans hle) (hi.trans hle) (hr.trans hle) (hf.trans hle)
  refine ⟨smin,pstar,β,lamList,ζ,δ,θ,α,κ,b,z,matchErr,σcap,κ',dNeed,hsEq,hs,hpEq,hp,hp1,hpρ,
    hβ,hβ1,hlam,hζ,hbudget,hδ,hδ1,hδsmall,hδcap,hθ,hθ1,hθδ,hαEq,hα,hκ,hb,hz,hmatchErr,hσcap,hσle,
    hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hphysical',?_⟩
  intro d hd hspace
  obtain ⟨ζret,hζret,hcapacity,hsize,hmass,Nmargin,hmargin⟩:=hplace d (by omega) hspace
  refine ⟨ζret,hζret,hcapacity,hsize,hmass,max Nbound Nmargin,by omega,?_,?_⟩
  · intro n hn
    obtain ⟨hD,hN⟩:=hboundary d hd n (by omega)
    obtain ⟨herror,hmargin'⟩:=hmargin n (by omega)
    exact ⟨hD,hN,herror,hmargin'⟩
  · intro K hK
    obtain ⟨lam,γ,a,hlamPos,hγPos,haPos,hlamθ,hγlam,hγκ,haκ,haBound,hrel0,hrelθ,hrelErr,hslack⟩:=
      ordinary_matching_mass_rates K hK θ κ' matchErr hθ (by linarith) hκ' hmatchErr
    have hlam1:lam≤1:=by linarith
    refine ⟨lam,a,γ,hlamPos,hlam1,haPos,hγPos,hlamθ,hγlam,haκ,hγκ,haBound,hrel0,hrelθ,hrelErr,hslack,?_⟩
    intro n
    exact hload a γ n (by positivity) haκ hγκ
end Oberwolfach
