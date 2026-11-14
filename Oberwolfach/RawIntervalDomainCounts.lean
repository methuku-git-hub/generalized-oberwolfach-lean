module

public import Oberwolfach.RawIntervalLabelGraphs
public import Oberwolfach.RawIntervalHubRestriction
public import Oberwolfach.NeighbourPairDomains

@[expose] public section

/-! Restriction to a fixed set of hub columns preserves the exact original
interval law. It does not condition on any realised graph event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem rawIntervalCommonHubsOnDomain_common_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (B:Finset U) (hB:0<B.card) (j:Color) (pH:ℝ) (hj:∀ u∈B,s u j=pH)
    {I:Type} [Fintype I] (T:I→Finset V)
    (hsep:∀ i,∀ x∈T i,∀ y∈T i,x≠y → ¬PermutationClose π (3*d) x y)
    (hT:∀ i,(T i).Nonempty) (k:ℕ) (hk:0<k) (hsize:∀ i,(T i).card≤k)
    (t:ℝ) (ht:0<t):
    1-(Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*B.card))))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ i,|((B.filter (fun u=>∀ v∈T i,
        rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))).card:ℝ)-pH^(T i).card*B.card|<t):=by
  have hh:=rawIntervalCommonHubs_common_event π d hd
    (fun u:B=>q u.val) (fun u=>hq u.val) (fun u=>hQ u.val)
    (fun u:B=>s u.val) (fun u=>hs u.val) (fun u=>hS u.val) hnoshort
    (by simpa only [Fintype.card_coe] using hB) j pH (fun u=>hj u.val u.property)
    T hsep hT k hk hsize t ht
  rw [←rawInterval_hub_restriction_probability (fun u:B=>u.val) Subtype.val_injective d hd q hq hQ s hs hS] at hh
  simp only [Fintype.card_coe] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ i
  have he:(Fintype.card {u:B//∀ v∈T i,
      rawIntervalFamilyState π d (fun z=>σ (z.1.val,z.2)) (v,u)=some (Sum.inr j)})=
      (B.filter (fun u=>∀ v∈T i,rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))).card:=by
    rw [Fintype.card_subtype]
    simpa only [rawIntervalFamilyState] using finite_domain_predicate_card B (fun u=>∀ v∈T i,
      rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j))
  have hi:=hσ i
  change |(Fintype.card {u:B//∀ v∈T i,
    rawIntervalFamilyState π d (fun z=>σ (z.1.val,z.2)) (v,u)=some (Sum.inr j)}:ℝ)-
      pH^(T i).card*B.card|<t at hi
  rw [he] at hi
  exact hi

end Oberwolfach
