module

public import Oberwolfach.ExpandedOrderedOrdinaryFiniteFamily
public import Oberwolfach.ExpandedMarkedFiniteFamily
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! One enriched outcome can satisfy every ordinary-type root estimate and
all roots of a marked type, without an independence assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_ordinary_marked_families_joint_highProbability
    (I J:Type) [Fintype I] [Fintype J] (d:ℕ) (hd:2≤d) (m:I→ℕ) (hm:∀ i,2≤m i)
    (B t:I→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i)
    (mK:ℕ) (hmK:3≤mK) (BK tK:ℝ) (hBK:0<BK) (htK:0<tK):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:∀ i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i))
    (g:I→Γ) (j:I→Color) (H₀ Hₖ:V→U→Prop)
    (wK:∀ k:J,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mK π (3*d) H₀ Hₖ→ℝ)
    (hwK:∀ k W,0≤wK k W ∧ wK k W≤BK/(Fintype.card V:ℝ)^mK) (gK:J→Γ) (jK:J→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let O:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i
    let K:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ k root,
      |typedMarkedPotentialLoad (wK k) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gK k) (jK k)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wK k W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gK k) (jK k) a|<tK;
    (999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>O z ∧ K z):=by
  obtain ⟨NO,hO⟩:=raw_expanded_ordinary_finite_family_highProbability I d hd m hm B t hB ht (1/4000) (by norm_num)
  obtain ⟨NK,hK⟩:=raw_expanded_marked_finite_family_highProbability J d mK hd hmK BK tK (1/4000) hBK htK (by norm_num)
  refine ⟨max NO NK,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j H₀ Hₖ wK hwK gK jK F _ ν μ f O K
  let law:=μ.sigma (fun ω=>ν (f ω))
  have hO':1-(1:ℝ)/4000≤law.probability O:=
    hO V U Γ Color ((le_max_left _ _).trans hn) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j F ν
  have hK':1-(1:ℝ)/4000≤law.probability K:=
    hK V U Γ Color ((le_max_right _ _).trans hn) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ wK hwK gK jK F ν
  have hh:=finiteLaw_good_intersection law O K (1/4000) hK'
  linarith [hO']
end Oberwolfach
