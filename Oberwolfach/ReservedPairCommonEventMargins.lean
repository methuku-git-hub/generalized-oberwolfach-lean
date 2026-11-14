module

public import Oberwolfach.ReservedPairMatchingHypotheses

@[expose] public section
/-! The common pair test yields many eligible outer hubs at host scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_pair_common_event_hypotheses
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (inner:Finset U) (Old:U→Finset (Fin n))
    (hOld:∀w,Disjoint (rawReservedSpokeList π d σ w) (Old w))
    (Kbad:SimpleGraph (Fin n)) (Bad:Fin n→Finset U)
    (ρ:ℝ) (hρ:0≤ρ) (hU:ρ*n≤Fintype.card U)
    (hinner:(inner.card:ℝ)≤ρ*n/80000)
    (herror:(n:ℝ)^(3/4:ℝ)≤ρ*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ)):
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner
    (∀e,Disjoint (Lbad e) inner) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,(ρ/40000)*n≤((Lbad e).card:ℝ)):=by
  intro Lbad
  have hmargin:(ρ/40000)*n+inner.card≤(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ):=by
    nlinarith
  exact reserved_pair_matching_hypotheses π d σ inner Old hOld Kbad Bad (ρ/40000)
    ((5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U) ((n:ℝ)^(3/4:ℝ)) hmargin hpair
end Oberwolfach
