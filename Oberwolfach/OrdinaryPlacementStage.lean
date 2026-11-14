module

public import Oberwolfach.OrdinaryPlacementHierarchyBeforeMatching

@[expose] public section
/-! A named stage of the early reserved-placement hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryPlacementStage
    (m dNeed:ℕ) (α lamList ζList capEdit δ θ κ b z matchErr σ κ':ℝ):Prop :=

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

end Oberwolfach
