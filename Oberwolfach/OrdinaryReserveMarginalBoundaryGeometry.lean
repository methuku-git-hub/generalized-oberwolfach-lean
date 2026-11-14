module

public import Oberwolfach.OrdinaryAssignedVortexMarginalFloor
public import Oberwolfach.OrdinaryAbundanceMatchingGeometryAtLeast
public import Oberwolfach.OrdinaryBoundaryLoadSpacing

@[expose] public section
/-! Choose the abundant reserve and the common marginal floor before choosing
spacing; then choose spacing for both the matching geometry and boundary load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserve_marginal_boundary_geometry
    (β θ ρ₀ δ:ℝ) (hβ:0<β) (hθ:0<θ) (hρ₀:0<ρ₀) (hδ:0<δ)
    (rstar m:ℕ):
    ∃smin pmin:ℝ, smin=β/200 ∧ 0<smin ∧ 0<pmin ∧ pmin≤1 ∧ pmin≤ρ₀*smin ∧
    (∀{n D K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (i₀:Fin K) (rsv θ' c:ℝ) (d:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ' c ρ₀ smin d),
      pmin≤2*(initialIndexDensity U D*rsv/2) ∧ pmin≤rsv ∧ rsv≤1 ∧
      2*(initialIndexDensity U D*rsv/2)=initialIndexDensity U D*rsv ∧
      (∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ' c w false=rsv)) ∧
    ∀dNeed:ℕ,∃d K rank N:ℕ,dNeed≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      1≤N ∧ ∀n≥N,4/(d:ℝ)≤δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/16 :=by
  have hsmin:0<β/200:=by positivity
  obtain ⟨pmin,hpmin,hpmin1,hpminR,hfloor⟩:=ordinary_assigned_vortex_marginal_floor ρ₀ (β/200) hρ₀ hsmin
  obtain ⟨d₀,N,hd₀,hN,hbound⟩:=ordinary_boundary_load_spacing_and_order δ hδ
  refine ⟨β/200,pmin,rfl,hsmin,hpmin,hpmin1,hpminR,hfloor,?_⟩
  intro dNeed
  obtain ⟨d,K,rank,hneed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap⟩:=
    ordinary_abundance_matching_geometry_at_least β θ hβ hθ rstar m (max d₀ dNeed)
  refine ⟨d,K,rank,N,le_trans (le_max_right _ _) hneed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hN,?_⟩
  intro n hn
  exact hbound d (le_trans (le_max_left _ _) hneed) n hn
end Oberwolfach
