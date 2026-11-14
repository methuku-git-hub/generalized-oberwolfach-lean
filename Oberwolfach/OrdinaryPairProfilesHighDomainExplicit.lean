module

public import Oberwolfach.OrdinaryPairProfilesForLargeOrder
public import Oberwolfach.OrdinaryLocalCycleFintypes

@[expose] public section
/-! Apply the existing profile theorem to the identical high-instance hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_pair_profiles_from_high_domain_explicit (m:ℕ) (hm:3≤m)
    (β a B η L:ℝ) (hβ:0<β) (hL:0≤L):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (Q F:SimpleGraph V) (H:V→U→Prop),
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ u u' v w,β*Fintype.card V≤
      ((ordinaryHubDomainHigh H u u'∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) →
    ∀ w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (ordinaryHubDomainHigh H u u') (m+1)→ℝ,
    (∀ u u' (hne:u≠u') C,a/(Fintype.card V:ℝ)^m≤w u u' hne C ∧ w u u' hne C≤B/(Fintype.card V:ℝ)^m) →
    (∀ u u' (hne:u≠u'),∀ v∈ordinaryHubDomainHigh H u u',
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) →
    Nonempty (OrdinaryCommonCycleProfiles Q F H (m+1) (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β
      ((ordinaryLocalCountCoeff m β/2)^(m+2)) a B η) := by
  obtain ⟨N,hN⟩:=ordinary_pair_profiles_for_large_order m hm β a B η L hβ hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q F H hF hpair w hw hdeg
  obtain ⟨wlow,hwlow,hdlow⟩:=ordinary_local_weights_transport_explicit Q F (m+1)
    (ordinaryHubDomainHigh H) (ordinaryHubDomainLow H) (ordinary_hub_domains_equal H).symm
    (fun u u'=>ordinaryLocalCycleFintypeHigh Q F (ordinaryHubDomainHigh H u u') (m+1))
    (fun u u'=>ordinaryLocalCycleFintypeLow Q F (ordinaryHubDomainLow H u u') (m+1))
    (a/(Fintype.card V:ℝ)^m) (B/(Fintype.card V:ℝ)^m) η w hw hdeg
  refine hN V U hn Q F H hF ?_ wlow hwlow hdlow
  intro u u' v z
  have hh:=hpair u u' v z
  rw [←ordinary_hub_domains_equal H] at hh
  exact hh
end Oberwolfach
