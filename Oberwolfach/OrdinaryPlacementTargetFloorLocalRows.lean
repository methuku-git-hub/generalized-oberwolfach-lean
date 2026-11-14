module

public import Oberwolfach.OrdinaryProportionalPlacementTargetFloor
public import Oberwolfach.OrdinaryPlacementRatesProportionalBeforeSpacing
public import Oberwolfach.OrdinaryReservedMatchingLoadRate
public import Oberwolfach.OrdinaryMatchingMassRates
public import Oberwolfach.OrdinaryBoundaryLoadSpacing

@[expose] public section
/-! The reserved-list rate may be fixed before vortex geometry, while the
matching and placement rates are chosen only after the desired edit cap. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_target_floor_local_rows
    (m:ℕ) (lamList ζList α cap:ℝ)
    (hlam:0<lamList) (hlam1:lamList≤1) (hζ:0<ζList) (hα:0<α) (hcap:0<cap):
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      0<δ ∧ δ≤1 ∧ δ≤((lamList/2)/100)^2 ∧ 5*Real.sqrt δ≤cap ∧
      0<θ ∧ θ≤1/100 ∧ θ≤δ/8 ∧ 0<κ ∧ 0<b ∧ 0<z ∧ 0<matchErr ∧
      0<σ ∧ σ≤cap ∧ min (α/4096) (1/2:ℝ)*θ≤b ∧ min (1/1024:ℝ) (min (α/4096) (1/2:ℝ)/8)*θ≤z ∧ b≤ζList ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧ 0<κ' ∧ κ'≤κ ∧ 2≤dNeed ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→
        edit≤σ*n→inner≤σ*n→ reserve≤σ*n→conflict≤σ*n→
        edit+2*inner+reserve+conflict≤b*n) ∧
    ∀(d:ℕ),dNeed≤d→1/(4*(d:ℝ))≤5*θ^2/256→
      ∃ζret:ℝ,0<ζret ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+matchErr≤(δ/8)/2 ∧
      ∃N:ℕ,1≤N ∧ (∀n:ℕ,N≤n→4/(d:ℝ)≤δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/16) ∧
    ∀K:ℕ,0<K→∃lam a γ:ℝ,0<lam ∧ lam≤1 ∧ 0<a ∧ 0<γ ∧
      lam≤θ/10 ∧ γ≤lam/10 ∧ a≤κ' ∧ γ≤κ' ∧ a≤b/16 ∧ a≤z/16 ∧ γ≤z/16 ∧ γ≤θ ∧
      a≤θ/(1600*(K:ℝ)*(K:ℝ)) ∧
      0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 ∧
      lam+γ*(1-θ+lam)≤matchErr ∧ lam+γ*(1-θ+lam)<θ ∧
      ∀n:ℕ,2*((max a γ)*n)≤δ*n/8 :=by
  obtain ⟨δ,hδ,hδsmall,hδcap⟩:=ordinary_placement_delta_from_target_rate (lamList/2) cap (by positivity) hcap
  have hf0:0≤(lamList/2)/100:=by positivity
  have hf1:(lamList/2)/100≤1:=by linarith
  have hfSq:((lamList/2)/100)^2≤1:=by nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hf1)]
  have hδ1:δ≤1:=hδsmall.trans hfSq
  let θ:ℝ:=min (δ/16) (min (1/200:ℝ) ζList)
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθ1:θ≤1/100:=(min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hθList:θ≤ζList:=(min_le_right _ _).trans (min_le_right _ _)
  have hθδ:θ≤δ/8:=(min_le_left _ _).trans (by linarith)
  obtain ⟨κ,b,z,matchErr,σ,hκ,hb,hz,hmatchErr,hσ,hblower,hzlower,hbζ,hbα,hbδ,hzb,hphysical,hplace⟩:=
    ordinary_placement_rates_proportional_target_floor m θ δ α ζList hθ hθ1 hδ hθδ hα hζ hθList
  obtain ⟨κ',hκ',hκ'κ,hκ'δ,hload⟩:=ordinary_reserved_matching_load_rate δ κ hδ hκ
  obtain ⟨dNeed,Nbound,hdNeed,hNbound,hboundary⟩:=ordinary_boundary_load_spacing_and_order δ hδ
  let σcap:=min σ cap
  have hσcap:0<σcap:=lt_min hσ hcap
  have hσle:σcap≤cap:=min_le_right _ _
  have hphysical':∀(n edit inner reserve conflict:ℝ),0≤n→
      edit≤σcap*n→inner≤σcap*n→ reserve≤σcap*n→conflict≤σcap*n→
      edit+2*inner+reserve+conflict≤b*n:=by
    intro n edit inner reserve conflict hn he hi hr hf
    have hle:=mul_le_mul_of_nonneg_right (min_le_left σ cap) hn
    exact hphysical n edit inner reserve conflict hn (he.trans hle) (hi.trans hle) (hr.trans hle) (hf.trans hle)
  refine ⟨δ,θ,κ,b,z,matchErr,σcap,κ',dNeed,hδ,hδ1,hδsmall,hδcap,hθ,hθ1,hθδ,
    hκ,hb,hz,hmatchErr,hσcap,hσle,hblower,hzlower,hbζ,hbα,hbδ,hzb,hκ',hκ'κ,hdNeed,hphysical',?_⟩
  intro d hd hspace
  obtain ⟨ζret,hζret,hcapacity,hsize,hmass⟩:=hplace d (by omega) hspace
  refine ⟨ζret,hζret,hcapacity,hsize,hmass,Nbound,hNbound,?_,?_⟩
  · intro n hn
    exact hboundary d hd n hn
  · intro K hK
    let κcap:ℝ:=min κ' (min (b/16) (z/16))
    have hκcap:0<κcap:=by dsimp [κcap];positivity
    have hκcapκ:κcap≤κ':=min_le_left _ _
    have hκcapb:κcap≤b/16:=(min_le_right _ _).trans (min_le_left _ _)
    have hκcapz:κcap≤z/16:=(min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨lam,γ,a,hlamPos,hγPos,haPos,hlamθ,hγlam,hγκ,haκ,haBound,hrel0,hrelθ,hrelErr,hslack⟩:=
      ordinary_matching_mass_rates K hK θ κcap matchErr hθ (by linarith) hκcap hmatchErr
    have hlam1':lam≤1:=by linarith
    have haκ':a≤κ':=haκ.trans hκcapκ
    have hγκ':γ≤κ':=hγκ.trans hκcapκ
    have hab:a≤b/16:=haκ.trans hκcapb
    have haz:a≤z/16:=haκ.trans hκcapz
    have hγz:γ≤z/16:=hγκ.trans hκcapz
    have hγθ:γ≤θ:=by linarith
    refine ⟨lam,a,γ,hlamPos,hlam1',haPos,hγPos,hlamθ,hγlam,haκ',hγκ',hab,haz,hγz,hγθ,haBound,hrel0,hrelθ,hrelErr,hslack,?_⟩
    intro n
    exact hload a γ n (by positivity) haκ' hγκ'
end Oberwolfach
