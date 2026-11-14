module

public import Oberwolfach.OrdinaryRecodedListRateChoice

@[expose] public section
/-! The placement list has its own rates.  Choose them from the genuine
reserve floor before choosing the unrelated matching tolerance. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_rates_before_matching
    (γ ρ₀ smin:ℝ) (hγ:0<γ) (hρ:0<ρ₀) (hs:0<smin):
    ∃β lam ζ:ℝ, 0<β ∧ β≤1 ∧ 0<lam ∧ 0<ζ ∧ lam+2*ζ≤β ∧
    ∃dMin:ℕ,2≤dMin ∧ ∀d:ℕ,dMin≤d→
      ∃N:ℕ,∀n:ℕ,N≤n→
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γ*(ρ₀*smin/2)^2*n ∧
        β*n+(n:ℝ)^(3/4:ℝ)≤γ*(ρ₀*smin/2)^2*n*smin ∧
        (lam+2*ζ)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤β*n :=by
  have hp:0<ρ₀*smin/2:=by positivity
  obtain ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,dMin,hdMin,hbase⟩:=
    ordinary_recoded_list_rate_choice γ (ρ₀*smin/2) smin hγ hp hs
  obtain ⟨N₀,hN₀⟩:=hbase dMin le_rfl
  let n₀:=max N₀ 1
  have hn:(0:ℝ)<n₀:=by exact_mod_cast (show 0<n₀ by dsimp [n₀];omega)
  have hrest:0≤((n₀:ℝ)+2*(n₀:ℝ)^(3/4:ℝ))/dMin:=by positivity
  have hb:= (hN₀ n₀ (le_max_left _ _)).2.2
  have hbudget:lam+2*ζ≤β:=by nlinarith
  refine ⟨β,lam,ζ,hβ,hβ1,hlam,hζ,hbudget,dMin,hdMin,?_⟩
  intro d hd
  obtain ⟨N,hN⟩:=hbase d hd
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨h₁,h₂,h₃⟩:=hN n hn
  refine ⟨h₁,?_,h₃⟩
  have hcoef:0≤γ*(ρ₀*smin/2)^2*n:=by positivity
  nlinarith
end Oberwolfach
