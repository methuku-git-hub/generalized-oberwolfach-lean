module

public import Oberwolfach.OrderedOrdinarySampledHubTotals
public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Per-hub full ordinary candidate weights on the expanded sample, with
exact root-free expectations and any dependent second-stage law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem expanded_ordinary_sampled_hub_totals
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (hn:0<Fintype.card V) (huV:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ) (B:ℝ) (hB:0<B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color) (t:ℝ) (ht:0<t)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let C:=((m:ℝ)+1)^2*B;
    1-(Fintype.card U:ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))))≤
    (μ.sigma ν).probability (fun z=>∀hub,
      |orderedOrdinarySampledHubTotal P π d m w g j hub (fun e=>rawExpandedApproximateCollapse e (z.1 e))-
       ∑W,orderedOrdinaryHubWeight w hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t) :=by
  intro μ C
  let μraw:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS)
  let f:=fun (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedApproximateCollapse e (σ e)
  let Good:=fun σ:RawMarkedOutcome V U Γ Color=>∀hub,
      |orderedOrdinarySampledHubTotal P π d m w g j hub σ-
       ∑W,orderedOrdinaryHubWeight w hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t
  have hRaw:=ordered_ordinary_sampled_hub_total_common_event P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS m hm hn huV w B hB hw g j t ht
  have hRaw':1-(Fintype.card U:ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*C*(2*((m:ℝ)+1))*((Fintype.card V:ℝ)*C))))≤μraw.probability Good:=by
    simpa only [μraw,C,Good,ordered_ordinary_sampled_hub_total_expectation P π p₂ k₂ hp₂ hk₂ (by linarith) d hd q hq hQ s hs hS hnoshort m hm w g j] using hRaw
  have hProj:μ.map f=μraw:=by
    exact raw_expanded_approximate_wheel_law_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  have hMap:=finiteLaw_map_probability μ f Good
  rw [hProj] at hMap
  have hFirst:=finiteLaw_sigma_first_probability μ ν (fun σ=>Good (f σ))
  change _≤(μ.sigma ν).probability (fun z=>Good (f z.1))
  exact hFirst.symm ▸ hMap.symm ▸ hRaw'
end Oberwolfach
