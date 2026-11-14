module

public import Oberwolfach.OrdinaryPlacementRatesBeforeMatching
public import Oberwolfach.OrdinaryEarlyContractionTargetFloor

@[expose] public section
/-! Placement list rates and inner contraction are selected before the
matching tolerance, using the reserve floor from the original factors. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach

def OrdinaryEarlyLocalBudget (α ε:ℝ):Prop :=
  ∀(n:ℕ) (inner θ b a γ u t edit del LF aux:ℝ),
    0 ≤ inner → 0 ≤ θ → min (α/4096) (1/2:ℝ)*θ≤b→
    inner≤ε*n→a≤b/16→γ≤θ→u≤2*θ→t≤θ*inner→
    edit≤b*n/16→aux≤b*n/16→del≤b*n/16→2*LF≤b*n/16→
    edit+(max (a*n) (γ*inner)+u*inner+3*t+aux+del+LF)+LF≤b*n

def OrdinaryLaterPlacementGeometry (α lamList ζList:ℝ):Prop :=
  ∀(m:ℕ) (capEdit:ℝ),0<capEdit →
    ∃δ θ κ b z matchErr σ κ':ℝ,∃dNeed:ℕ,
      0<δ ∧ δ≤1 ∧ δ≤((lamList/2)/100)^2 ∧ 5*Real.sqrt δ≤capEdit ∧
      0<θ ∧ θ≤1/100 ∧ θ≤δ/8 ∧ 0<κ ∧ 0<b ∧ 0<z ∧ 0<matchErr ∧
      0<σ ∧ σ≤capEdit ∧ min (α/4096) (1/2:ℝ)*θ≤b ∧
      min (1/1024:ℝ) (min (α/4096) (1/2:ℝ)/8)*θ≤z ∧
      b≤ζList ∧ b≤α/16 ∧ b≤δ/8 ∧ z≤b/4 ∧ 0<κ' ∧ κ'≤κ ∧ 2≤dNeed ∧
      (∀(n edit inner reserve conflict:ℝ),0≤n→edit≤σ*n→inner≤σ*n→
        reserve≤σ*n→conflict≤σ*n→edit+2*inner+reserve+conflict≤b*n) ∧
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
      ∀n:ℕ,2*((max a γ)*n)≤δ*n/8

theorem ordinary_placement_hierarchy_before_matching
    (γ ρ₀ smin capInner:ℝ) (hγ:0<γ) (hρ:0<ρ₀) (hs:0<smin) (hcap:0<capInner):
    let α:=5*ρ₀*smin^2/128;
    ∃β lamList ζList ε:ℝ,
      0<β ∧ β≤1 ∧ 0<lamList ∧ 0<ζList ∧ lamList+2*ζList≤β ∧
      0<ε ∧ ε≤capInner ∧ ε≤lamList/4 ∧ ε≤ζList/8 ∧
      ε≤min (1/1024:ℝ) (min (α/4096) (1/2:ℝ)/8)/16 ∧
      OrdinaryEarlyLocalBudget α ε ∧ OrdinaryLaterPlacementGeometry α lamList ζList ∧
      ∃dMin:ℕ,2≤dMin ∧ ∀d:ℕ,dMin≤d→
      ∃N:ℕ,∀n:ℕ,N≤n→
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*(ρ₀*smin/2)^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*(ρ₀*smin/2)^2*n*smin ∧
        (lamList+2*ζList)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n :=by
  intro α
  have hα:0<α:=by dsimp [α];positivity
  obtain ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,hbudget,dMin,hdMin,hrates⟩:=
    ordinary_placement_rates_before_matching γ ρ₀ smin hγ hρ hs
  have hlam1:lam≤1:=by linarith
  obtain ⟨ε,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeometry⟩:=
    ordinary_early_contraction_target_floor α lam ζ capInner hα hlam hlam1 hζ hcap
  exact ⟨β,lam,ζ,ε,hβ,hβ1,hlam,hζ,hbudget,hε,hεcap,hεlam,hεζ,hεfloor,
    hlocal,hgeometry,dMin,hdMin,hrates⟩
end Oberwolfach
