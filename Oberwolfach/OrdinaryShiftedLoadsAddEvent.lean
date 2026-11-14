module

public import Oberwolfach.OrdinaryShiftedApproximateLoadsShared
public import Oberwolfach.ExpandedOrderedOrdinaryFiniteFamily
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The approximate marked and ordinary seed-load tests hold together,
with the same first sample and any dependent second sampling stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_shifted_approximate_loads_add_to_event
    (IM IO:Type) [Fintype IM] [Fintype IO] (d mM:ℕ) (hd:2≤d) (hmM:3≤mM)
    (mO:IO→ℕ) (hmO:∀i,2≤mO i) (BM tM:ℝ) (hBM:0<BM) (htM:0<tM)
    (BO tO:IO→ℝ) (hBO:∀i,0<BO i) (htO:∀i,0<tO i) (ζ:ℝ) (hζ:0<ζ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (H₀ Hₖ:V→U→Prop)
    (wM:∀i:IM,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mM π (3*d) H₀ Hₖ→ℝ)
    (hwM:∀i W,0≤wM i W ∧ wM i W≤BM/(Fintype.card V:ℝ)^mM)
    (gM:IM→Γ) (jM:IM→Color)
    (wO:∀i:IO,OrderedOrdinaryWheel (U:=U) π (3*d) (mO i+1)→ℝ)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(Fintype.card V:ℝ)^(mO i))
    (gO:IO→Γ) (jO:IO→Color)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E →
    1-(εE+ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      (∀i root,|typedMarkedPotentialLoad (wM i) (ordinaryShiftedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gM i) (jM i)) root-
        ∑W,(if root∈typedMarkedOccurrenceResources W then wM i W else 0)*
          ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ p₂ q s (gM i) (jM i) a|<tM) ∧
      (∀i root,|resourcePatternLoad orderedOrdinaryResources (wO i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (gO i) (jO i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑W,(if root∈orderedOrdinaryResources W then wO i W else 0)*
          ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gO i) (jO i) (orderedOrdinaryResourceEmbedding a)|<tO i)) :=by
  obtain ⟨N,hN⟩:=ordinary_shifted_approximate_loads_shared IM IO d mM hd hmM mO hmO BM tM hBM htM BO tO hBO htO ζ hζ
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ wM hwM gM jM wO hwO gO jO R _ ν E εE μ hE
  have hLoad:=hN V U Γ Color hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ wM hwM gM jM wO hwO gO jO ν
  have hh:=finiteLaw_intersection_lower (μ.sigma ν) E _ εE ζ hE hLoad
  simpa only [sub_add_eq_sub_sub] using hh
end Oberwolfach
