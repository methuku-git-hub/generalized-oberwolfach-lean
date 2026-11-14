module

public import Oberwolfach.FirstVortexMatchingLocalBudgetAfterScale
public import Oberwolfach.FirstVortexPreciseMatchingAndEditRates

@[expose] public section
/-! Choose the vortex scale before the (possibly scale-dependent) transfer
cap, then θ, spacing, matching rates, correction cap, and finally n. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem first_vortex_prepared_ordered_precise_parameters
    (a α C₀ εupper:ℝ) (ha:0<a) (hα:0<α) (hC:0<C₀) (hupper:0<εupper):
    ∃ε:ℝ,0<ε ∧ ε≤εupper ∧ ε≤1/4 ∧ ε≤a/8192 ∧ ε≤α/(1000*C₀) ∧
    ∀cap θupper:ℝ,0<cap→0<θupper→
    ∃θmax:ℝ,0<θmax ∧ θmax≤θupper ∧ θmax≤1/100 ∧ ∀θ:ℝ,0<θ→θ≤θmax→∀dmin:ℕ,
    ∃d:ℕ,dmin≤d ∧ 3≤d ∧ 1/(d:ℝ)≤θ/1024 ∧ ∀upper:ℝ,0<upper→
    ∃lamBase lamAssign ξCap:ℝ,
      0<lamBase ∧ 0<lamAssign ∧ lamBase≤lamAssign ∧ lamAssign≤upper ∧
      lamAssign≤1 ∧ lamAssign≤θ ∧ lamAssign≤α/128 ∧ lamAssign≤cap*a/4096 ∧ 0<ξCap ∧
      (∀ξ:ℝ,ξ≤ξCap→lamBase+ξ≤a*θ/4096 ∧ ξ/2≤(lamAssign-lamBase)*ε) ∧
      ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀(a' γ:ℝ),max a' γ≤1/(10*(d:ℝ))→
        2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a' γ*n≤cap*(ε*n)/128 ∧
        ∀E:ℕ,(E:ℝ)≤(θ*ε^2+lamAssign*ε)*(n:ℝ)^2+24*d*n→
          2*(⌈4*(E:ℝ)/(a*n)⌉₊:ℕ)≤cap*(ε*n)/128 :=by
  let ε:ℝ:=min εupper (min (1/4) (min (a/8192) (α/(1000*C₀))))
  have hε:0<ε:=by dsimp [ε];positivity
  have hεupper:ε≤εupper:=min_le_left _ _
  have hεquarter:ε≤1/4:=(min_le_right _ _).trans (min_le_left _ _)
  have hεa:ε≤a/8192:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεα:ε≤α/(1000*C₀):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε,hε,hεupper,hεquarter,hεa,hεα,?_⟩
  intro cap θupper hcap hθupper
  obtain ⟨θmax,hθmax,hθupper',hθsmall,hθ⟩:=first_vortex_matching_local_budget_after_scale cap a ε θupper hcap ha hε hεquarter hθupper
  refine ⟨θmax,hθmax,hθupper',hθsmall,?_⟩
  intro θ hθ0 hθmax' dmin
  obtain ⟨d,hdmin,hd,hspacing,hbudget⟩:=hθ θ hθ0 hθmax' dmin
  refine ⟨d,hdmin,hd,hspacing,?_⟩
  intro upper hUpper
  obtain ⟨lamBase,lamAssign,ξCap,hbase,hassign,hbasele,hup,h1,hθrate,hcaprate,hξ,hgap⟩:=
    first_vortex_precise_matching_and_edit_rates a cap θ ε (min upper (α/128)) ha hcap hθ0 hε (by positivity)
  obtain ⟨N,hN⟩:=hbudget lamAssign hassign.le h1 hcaprate
  refine ⟨lamBase,lamAssign,ξCap,hbase,hassign,hbasele,?_,h1,hθrate,?_,hcaprate,hξ,hgap,N,hN⟩
  · exact hup.trans (min_le_left _ _)
  · exact hup.trans (min_le_right _ _)
end Oberwolfach
