module

public import Oberwolfach.OrdinaryPairHubPatternConcentrationExt
public import Oberwolfach.OrdinaryDegreeNormalizedSeedBounds

@[expose] public section

/-! Simultaneous two-hub concentration for the actual degree-normalized
parent cycle weighting, chosen before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_seed_pattern_concentration
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hr:2≤r) (hd:2≤d)
    (hn:0<Fintype.card V) (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0<B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (D:ℝ) (hD:(Fintype.card V:ℝ)/2≤D)
    (ρ:Sym2 V→ℝ) (hρ:∀ e,0≤ρ e) (hρ1:∀ e,ρ e≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS)
    let w:=ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2)
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let err:=(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((r:ℝ)^4*(4*B)/Fintype.card V)*(2*r)*((r:ℝ)^2*(4*B)))));
    1-(Fintype.card (U×U):ℝ)*err≤μ.probability (fun σ=>∀ u u' root,
      |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))-
        μ.expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root (ordinaryResourceState (rawWheelGraph P τ) (ordinaryPairHubSpokes π d τ j u u')))|<t) := by
  intro μ w C err
  have hw:=ordinary_degree_normalized_seed_bounds P F r hr hn weight hweight B hB.le hb D hD
  exact ordinary_pair_hub_pattern_load_common_event_ext P F π r d hr hd hn w (4*B) (by positivity) hw
    ρ hρ hρ1 q hq hQ s hs hS j t ht
end Oberwolfach
