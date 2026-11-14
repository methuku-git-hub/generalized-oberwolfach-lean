module

public import Oberwolfach.OrdinaryTriangleProfilesForLargeOrder
public import Oberwolfach.OrdinaryLocalCycleFintypes

@[expose] public section
/-! Apply the triangular profile theorem using the equivalent high-instance hub domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable

theorem ordinary_triangle_profiles_from_high_domain_explicit
    (β a B η L:ℝ) (hβ:0<β) (hL:0≤L):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → ∀ (Q F:SimpleGraph V) (H:V→U→Prop),
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ u u' x y z w,β*Fintype.card V≤
      ((Finset.univ.filter (fun v=>H v u∧H v u'∧Q.Adj x v∧Q.Adj y v∧Q.Adj z v∧Q.Adj w v)).card:ℝ)) →
    ∀ w:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (ordinaryHubDomainHigh H u u') 3→ℝ,
    (∀ u u' (hne:u≠u') C,a/(Fintype.card V:ℝ)^2≤w u u' hne C ∧ w u u' hne C≤B/(Fintype.card V:ℝ)^2) →
    (∀ u u' (hne:u≠u'),∀ v∈ordinaryHubDomainHigh H u u',
      |1-hypergraphWeightedDegree localOrdinaryVertices (w u u' hne) v|≤η) →
    Nonempty (OrdinaryCommonCycleProfiles Q F H 3 (fun (_:Unit)=>pairedAbsorberTemplate 3) β
      ((ordinaryLocalCountCoeff 2 β/2)^4) a B η) := by
  obtain ⟨N,hN⟩:=ordinary_triangle_profiles_for_large_order β a B η L hβ hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q F H hF hfour w hw hdeg
  obtain ⟨wlow,hwlow,hdlow⟩:=ordinary_local_weights_transport_explicit Q F 3
    (ordinaryHubDomainHigh H) (ordinaryHubDomainLow H) (ordinary_hub_domains_equal H).symm
    (fun u u'=>ordinaryLocalCycleFintypeHigh Q F (ordinaryHubDomainHigh H u u') 3)
    (fun u u'=>ordinaryLocalCycleFintypeLow Q F (ordinaryHubDomainLow H u u') 3)
    (a/(Fintype.card V:ℝ)^2) (B/(Fintype.card V:ℝ)^2) η w hw hdeg
  refine hN V U hn Q F H hF ?_ wlow hwlow hdlow
  intro u u' x y z w
  convert hfour u u' x y z w using 1 <;> congr!
end Oberwolfach
