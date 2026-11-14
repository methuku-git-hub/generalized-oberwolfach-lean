module

public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! Root-omitted marked potential concentration for approximate physical
states, on the common enriched sample after selected-colour retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_approximate_marked_potentials_event
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:3≤m) (H₀ Hₖ:V→U→Prop) (hn:0<Fintype.card V) (huV:Fintype.card U≤Fintype.card V)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (B:ℝ) (hB:0<B) (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (g:Γ) (j:Color) (t:ℝ) (ht:0<t)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^4*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ root,
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j a|<t):=by
  intro μ f
  let E:=fun σ:RawMarkedOutcome V U Γ Color=>∀ root,
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j a|<t
  have hpEvent:=rawMarkedPotentialLoad_common_event P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ hn huV w B hB hw g j t ht
  have heq: (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>rawExpandedApproximateCollapse e (z.1 e)))=
      (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)).probability E:=
    raw_expanded_approximate_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν E
  change _≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>E (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
  rw [heq]
  exact hpEvent
end Oberwolfach
