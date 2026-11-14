module

public import Oberwolfach.OrderedOrdinaryHubWeightBound
public import Oberwolfach.ResourceFullPatternExpectation
public import Oberwolfach.OrderedOrdinaryWheelExpectation
public import Oberwolfach.OrderedOrdinaryLocality
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Concentration and exact means for full ordinary-wheel weight at each
hub, on the original marked-interval and physical-edge experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def orderedOrdinarySampledHubTotal (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (g:Γ) (j:Color) (u:U)
    (σ:RawMarkedOutcome V U Γ Color):ℝ :=
  resourceFullPatternLoad orderedOrdinaryResources (orderedOrdinaryHubWeight w u)
    (fun _ _=>true) (orderedOrdinaryResourceState P π d g j σ)

theorem ordered_ordinary_sampled_hub_total_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (g:Γ) (j:Color) (u:U):
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).expectation
      (orderedOrdinarySampledHubTotal P π d m w g j u)=
    ∑W,orderedOrdinaryHubWeight w u W *
      ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a) :=by
  let μ:=rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS
  have hh:=resource_full_pattern_supported_expectation μ orderedOrdinaryResources (orderedOrdinaryHubWeight w u)
    (fun _ _=>true) (orderedOrdinaryResourceCoordinates π d) (orderedOrdinaryResourceState P π d g j)
    (orderedOrdinary_resource_supported P π d g j)
    (by intro W a ha b hb hab;exact orderedOrdinaryCoordinates_disjoint d (by omega) W a b ha hb hab)
  change (FiniteLaw.pi μ).expectation (fun σ=>resourceFullPatternLoad orderedOrdinaryResources (orderedOrdinaryHubWeight w u)
    (fun _ _=>true) (orderedOrdinaryResourceState P π d g j σ))=_
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact rawMarkedResource_probability P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j (orderedOrdinaryResourceEmbedding a)

theorem ordered_ordinary_sampled_hub_total_common_event
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (m:ℕ) (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (B:ℝ) (hB:0<B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
    let C:=((m:ℝ)+1)^2*B
    1-(Fintype.card U:ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))))≤
    μ.probability (fun σ=>∀u,|orderedOrdinarySampledHubTotal P π d m w g j u σ-
      μ.expectation (orderedOrdinarySampledHubTotal P π d m w g j u)|<t) :=by
  intro μ C
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hC:0<C:=by dsimp [C];positivity
  have htail (u:U):
      μ.probability (fun σ=>t≤|orderedOrdinarySampledHubTotal P π d m w g j u σ-
        μ.expectation (orderedOrdinarySampledHubTotal P π d m w g j u)|)≤
      2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))) :=by
    have hh:=resource_full_pattern_supported_tail
      (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS) orderedOrdinaryResources
      (orderedOrdinaryHubWeight w u) (ordered_ordinary_hub_weight_nonneg w (fun W=>(hw W).1) u)
      (fun _ _=>true) (orderedOrdinaryResourceCoordinates π d)
      (orderedOrdinaryResourceState P π d g j) (orderedOrdinary_resource_supported P π d g j)
      (8*(d:ℝ)+6) (by positivity)
      (by intro a;exact_mod_cast orderedOrdinaryResourceCoordinates_card π d a)
      (by intro e;exact_mod_cast orderedOrdinaryResourceCoordinates_reverse_card π d e)
      (2*((m:ℝ)+1)) ((Fintype.card V:ℝ)*C) C (by positivity) (by positivity) hC
      (by intro W;exact_mod_cast orderedOrdinaryResources_card W)
      (ordered_ordinary_hub_weight_total_bound hm hn hu w B hB.le hw u)
      (ordered_ordinary_hub_weight_incidence_bound hm hn hu w B hB.le hw u) t ht
    exact hh
  have hh:=finiteLaw_common_event_lower μ Finset.univ
    (fun u σ=>t≤|orderedOrdinarySampledHubTotal P π d m w g j u σ-
      μ.expectation (orderedOrdinarySampledHubTotal P π d m w g j u)|)
    (fun _=>2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))))
    (fun u _=>htail u)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] using hh
end Oberwolfach
