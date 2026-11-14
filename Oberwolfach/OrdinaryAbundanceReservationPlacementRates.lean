module

public import Oberwolfach.OrdinaryPlacementOriginalSpacingRates
public import Oberwolfach.OrdinaryAbundanceMatchingReservation

@[expose] public section
/-! The original abundance supplies a reservation using a spacing that also
admits the required forced-placement rates, including protected targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_abundance_reservation_with_placement_rates
    (β θ δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hθ:0<θ) (hθsmall:θ≤1/100)
    (hδ:0<δ) (hθδ:θ≤δ/8) (rstar m:ℕ) (hr:3≤rstar):
    ∃d K rank:ℕ,2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤β ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    (∀α:ℝ,0<α→∃κ b z ζ matchErr:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ 0<ζ ∧ 0<matchErr ∧
      b≤α/16 ∧ b≤δ/8 ∧
      16/(d:ℝ)+16*κ+16*b/α+4*z≤θ/8 ∧
      2*θ+δ/8+((m:ℝ)+2)*κ≤δ ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤(δ/8)/2) ∧
    ∃smin:ℝ,0<smin ∧ ∃N:ℕ,∀n≥N,∀(U:Type) [Fintype U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hfreq:∀u,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ)),
    ∃(i₀:Fin K) (s:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤s ∧ s≤1/100 ∧ s≤1/(2*(K:ℝ)) ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=s*n) ∧
      (∀u,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n):=by
  obtain ⟨d,K,rank,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,smin,hsmin,N,hres⟩:=
    ordinary_abundance_matching_reservation β θ hβ hβ1 hθ rstar m hr
  refine ⟨d,K,rank,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,?_,smin,hsmin,N,hres⟩
  intro α hα
  exact ordinary_forced_placement_rates_from_abundance_spacing m d (by omega) θ δ α hθ hθsmall hδ hθδ hα hspace
end Oberwolfach
