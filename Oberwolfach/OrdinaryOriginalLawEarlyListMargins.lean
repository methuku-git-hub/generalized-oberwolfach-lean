module

public import Oberwolfach.OrdinaryPlacementHierarchyBeforeMatching
public import Oberwolfach.OrdinaryAssignedReservoirRateInputs

@[expose] public section
/-! The placement rates can be fixed before the matching tolerance and
before the actual factors are selected, using the original sampling law. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_law_early_list_margins
    (γ ρ₀ smin capInner:ℝ) (hγ:0<γ) (hρ:0<ρ₀) (hs:0<smin) (hcap:0<capInner):
    let α:=5*ρ₀*smin^2/128;
    let pstar:=ρ₀*smin/2;
    ∃β lamList ζList ε:ℝ,
      0<β ∧ β ≤ 1 ∧ 0<lamList ∧ 0<ζList ∧ lamList+2*ζList ≤ β ∧
      0<ε ∧ ε ≤ capInner ∧ ε ≤ lamList/4 ∧ ε ≤ ζList/8 ∧
      ε ≤ min (1/1024:ℝ) (min (α/4096) (1/2:ℝ)/8)/16 ∧
      OrdinaryEarlyLocalBudget α ε ∧ OrdinaryLaterPlacementGeometry α lamList ζList ∧
      ∃dMin:ℕ,2 ≤ dMin ∧ ∀d:ℕ,dMin ≤ d → 
      ∃N:ℕ,∀n:ℕ,N ≤ n → 
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1) ≤ γ*pstar^2*n ∧
      β*n+(n:ℝ)^(3/4:ℝ) ≤ γ*pstar^2*n*smin ∧
      (lamList+2*ζList)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d ≤ β*n ∧
      ∀{q K D:ℕ} (F:Fin q → SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
       (P:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
       (i₀:Fin K) (rsv θ c:ℝ),
       ρ₀ ≤ initialIndexDensity (Fin q) D → (1/2:ℝ)*(n:ℝ) ≤ D → 
       ∀sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
       let p:=initialIndexDensity (Fin q) D*rsv/2;
       ρ₀*n ≤ 4*(q:ℝ) ∧ pstar ≤ p ∧ pstar ≤ 2*p ∧ pstar ≤ rsv ∧ rsv ≤ 1 ∧
       2*p=initialIndexDensity (Fin q) D*rsv ∧
       (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv) ∧
       (∀w,ordinaryAssignedMarkedProbability F hF K θ c w false=0) :=by
  intro α pstar
  obtain ⟨β,lam,ζ,ε,hβ,hβ1,hlam,hζ,hbudget,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeom,dMin,hdMin,hrates⟩:=
    ordinary_placement_hierarchy_before_matching γ ρ₀ smin capInner hγ hρ hs hcap
  refine ⟨β,lam,ζ,ε,hβ,hβ1,hlam,hζ,hbudget,hε,hεcap,hεlam,hεζ,hεfloor,hlocal,hgeom,dMin,hdMin,?_⟩
  intro d hd
  obtain ⟨N,hN⟩:=hrates d hd
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨herr,hmargin,hlist⟩:=hN n hn
  refine ⟨herr,hmargin,hlist,?_⟩
  intro q K D F hF P hP hD i₀ rsv θ c hρlo hdegree sampling p
  have hpstar:0 ≤ pstar:=by dsimp [pstar];positivity
  have hpmin:2*pstar ≤ ρ₀*smin:=by dsimp [pstar];nlinarith
  have h:=ordinary_assigned_reservoir_rate_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin pstar d
    hρ hρlo hdegree hpstar hpmin sampling
  simpa only [Fintype.card_fin] using h
end Oberwolfach
