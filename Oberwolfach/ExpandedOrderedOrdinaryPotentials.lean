module

public import Oberwolfach.OrderedOrdinaryPotentialConcentration
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! Lift the ordinary directed-cycle potential event to the same enriched
experiment, preserving the selected-layer retention law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_approximate_ordered_potentials_event
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (hn:0<Fintype.card V) (huV:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (B:ℝ) (hB:0<B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color) (t:ℝ) (ht:0<t)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-(Fintype.card ((V×V)⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ root,
      |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d g j (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t):=by
  intro μ f
  let E:=fun σ:RawMarkedOutcome V U Γ Color=>∀ root,
      |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ)-
        ∑ W,(if root∈orderedOrdinaryResources W then w W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t
  have hpEvent:=orderedOrdinary_potential_common_event P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS
    m hm hn huV w B hB hw g j t ht
  have hpEvent':1-(Fintype.card ((V×V)⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
      (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)).probability E:=by
    simpa only [orderedOrdinary_potential_expectation P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS hnoshort (m+1) (by omega) w g j] using hpEvent
  have heq:(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>rawExpandedApproximateCollapse e (z.1 e)))=
      (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)).probability E:=
    raw_expanded_approximate_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν E
  change _≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
  rw [heq]
  exact hpEvent'
end Oberwolfach
