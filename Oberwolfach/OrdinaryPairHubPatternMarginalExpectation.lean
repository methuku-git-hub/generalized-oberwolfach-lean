module

public import Oberwolfach.OrdinaryPairHubPatternExpectation

@[expose] public section

/-! Exact omitted-root expectation on the two-hub common-spoke class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_pattern_marginal_expectation
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hd:2≤d)
    (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (w:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r→ℝ)
    (ρ:Sym2 V→ℝ) (hρ:∀ e,0≤ρ e) (hρ1:∀ e,ρ e≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (u u':U) (hne:u≠u') (root:Sym2 V⊕(V×Unit)):
    let μ:=rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS;
    (FiniteLaw.pi μ).expectation (fun σ=>
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root
        (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u')))=
      ∑ W,(if root∈ordinaryWheelResources W then w W else 0)*
        ∏ a∈ordinaryWheelResources W\{root},ordinaryPairHubMarginal P ρ s j u u' a := by
  intro μ
  have hh := ordinary_pair_hub_pattern_load_expectation P F π r d hF w μ j u u' root
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  congr 1
  exact Finset.prod_congr rfl (fun a _=>ordinary_pair_hub_resource_probability P π d hd ρ hρ hρ1 q hq hQ s hs hS hnoshort j u u' hne a)
end Oberwolfach
