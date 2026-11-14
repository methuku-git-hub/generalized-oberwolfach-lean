module

public import Oberwolfach.MarkedInitialInnerHubBound
public import Oberwolfach.ReservedPairCommonEventMargins
public import Oberwolfach.RetainedMarkedAbsorberBudget

@[expose] public section
/-! Construct the matching labels and forbidden hubs from the common event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_matching_labels_at_first_vortex_level
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (P:SimpleGraph (Fin n)) (Dv mv:ℕ) (βv εv:ℝ) (Q:Vortex U P Dv βv εv mv)
    (hεv:0≤εv) (Old:U→Finset (Fin n))
    (hOld:∀w,Disjoint (rawReservedSpokeList π d σ w) (Old w))
    (Kbad:SimpleGraph (Fin n)) (ρ:ℝ) (hρ:0≤ρ) (hUlo:ρ*n≤Fintype.card U)
    (hεsmall:εv≤ρ/80000) (herror:(n:ℝ)^(3/4:ℝ)≤ρ*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ))
    (m b:ℝ) (hm:0<m) (hb:0≤b) (hU:Fintype.card U≤n)
    (hM:4/m≤b/2) (hN:4*(n:ℝ)^(3/4:ℝ)≤b*n/2)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ)):
    let inner:=Q.extendedIndices 1
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner
    let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d σ t J w)
    (∀e,Disjoint (Lbad e) inner) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,(ρ/40000)*n≤((Lbad e).card:ℝ)) ∧
    (∀v,((Bad v).card:ℝ)≤b*n):=by
  intro inner Lbad Bad
  have hinner:(inner.card:ℝ)≤ρ*n/80000:=by
    have hh:=marked_initial_inner_hub_bound P Dv mv βv εv Q hεv (by simpa using hU)
    have hh':=mul_le_mul_of_nonneg_right hεsmall (Nat.cast_nonneg n)
    simp only [Fintype.card_fin] at hh
    nlinarith
  obtain ⟨hOutside,hShield,hLabels⟩:=reserved_pair_common_event_hypotheses π d σ inner Old hOld Kbad Bad ρ hρ hUlo hinner herror hpair
  have hBad:=retained_marked_absorber_budget π d σ t J m b hm hb hU hM hN hOcc
  exact ⟨hOutside,hShield,hLabels,hBad⟩
end Oberwolfach
