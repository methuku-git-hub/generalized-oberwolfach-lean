module

public import Oberwolfach.OrdinaryPlacementHierarchyBeforeMatching

@[expose] public section
/-! Early placement rates and their eventual margins, before matching
parameters and the sample are chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def OrdinaryPlacementEarlyRateData
    (γ ρ₀ smin capInner β lamList ζList ε:ℝ) (dMin:ℕ):Prop :=
  let α:=5*ρ₀*smin^2/128;
  0<β ∧ β ≤ 1 ∧ 0<lamList ∧ 0<ζList ∧ lamList+2*ζList ≤ β ∧
  0<ε ∧ ε ≤ capInner ∧ ε ≤ lamList/4 ∧ ε ≤ ζList/8 ∧
  ε ≤ min (1/1024:ℝ) (min (α/4096) (1/2:ℝ)/8)/16 ∧
  OrdinaryEarlyLocalBudget α ε ∧ OrdinaryLaterPlacementGeometry α lamList ζList ∧
  2 ≤ dMin ∧ ∀d:ℕ,dMin ≤ d → 
  ∃N:ℕ,∀n:ℕ,N ≤ n → 
    (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1) ≤ γ*(ρ₀*smin/2)^2*n ∧
    β*n+(n:ℝ)^(3/4:ℝ) ≤ γ*(ρ₀*smin/2)^2*n*smin ∧
    (lamList+2*ζList)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d ≤ β*n
end Oberwolfach
