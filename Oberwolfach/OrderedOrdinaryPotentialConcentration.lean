module

public import Oberwolfach.OrderedOrdinarySupportedTail
public import Oberwolfach.OrderedOrdinaryWheelExpectation
public import Oberwolfach.OrderedOrdinaryLoadBound
public import Oberwolfach.OrderedOrdinaryPairBound
public import Oberwolfach.OrderedOrdinaryLocality
public import Oberwolfach.CommonEvents

@[expose] public section
/-! A single concentration event for all ordinary-spoke and directed-rim
roots of the same ordered-cycle seed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem orderedOrdinary_potential_common_event
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (m:ℕ) (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (B:ℝ) (hB:0<B)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
    let F:=fun (σ:RawMarkedOutcome V U Γ Color) root=>resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ)
    1-(Fintype.card ((V×V)⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤
    μ.probability (fun σ=>∀ root,|F σ root-μ.expectation (fun τ=>F τ root)|<t):=by
  intro μ F
  have htail (root:(V×V)⊕(V×U)):
      μ.probability (fun σ=>t≤|F σ root-μ.expectation (fun τ=>F τ root)|)≤
        2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))):=by
    exact orderedOrdinary_supported_tail hm hn hu w B hB hw
      (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS) (orderedOrdinaryResourceCoordinates π d)
      (orderedOrdinaryResourceState P π d g j) (orderedOrdinary_resource_supported P π d g j)
      (8*(d:ℝ)+6) (by positivity)
      (by intro a; exact_mod_cast orderedOrdinaryResourceCoordinates_card π d a)
      (by intro e; exact_mod_cast orderedOrdinaryResourceCoordinates_reverse_card π d e)
      root t ht
  have hh:=finiteLaw_common_event_lower μ Finset.univ
    (fun root σ=>t≤|F σ root-μ.expectation (fun τ=>F τ root)|)
    (fun _=>2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))
    (fun root _=>htail root)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh
end Oberwolfach
