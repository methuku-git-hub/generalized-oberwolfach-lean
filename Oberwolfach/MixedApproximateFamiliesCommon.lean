module

public import Oberwolfach.MixedMarkedApproximateFamilyHigh
public import Oberwolfach.MixedOrdinaryApproximateFamilyHigh
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! Marked and ordinary approximate loads use one common retained outcome;
all candidate weights and their root-omitted products are left unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_approximate_families_common
    (IM IO:Type) [Fintype IM] [Fintype IO] (d mM:ℕ) (hd:2≤d) (hmM:3≤mM)
    (mO:IO→ℕ) (hmO:∀ i,2≤mO i) (BM tM:ℝ) (hBM:0<BM) (htM:0<tM)
    (BO tO:IO→ℝ) (hBO:∀ i,0<BO i) (htO:∀ i,0<tO i) (ζ:ℝ) (hζ:0<ζ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (H₀ Hₖ:V→U→Prop)
    (wM:∀ i:IM,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mM π (3*d) H₀ Hₖ→ℝ)
    (hwM:∀ i W,0≤wM i W ∧ wM i W≤BM/(Fintype.card V:ℝ)^mM)
    (gM jM:IM→Bool)
    (wO:∀ i:IO,OrderedOrdinaryWheel (U:=U) π (3*d) (mO i+1)→ℝ)
    (hwO:∀ i W,0≤wO i W ∧ wO i W≤BO i/(Fintype.card V:ℝ)^(mO i))
    (gO jO:IO→Bool) (a:Bool),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma (mixedClassActualRetention true π d a)).probability (fun z=>
      (∀ i root,
      |typedMarkedPotentialLoad (wM i) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gM i) (jM i)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wM i W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gM i) (jM i) a|<tM) ∧ (∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (wO i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (gO i) (jO i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then wO i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gO i) (jO i) (orderedOrdinaryResourceEmbedding a)|<tO i)):=by
  obtain ⟨NM,hM⟩:=mixed_marked_approximate_family_highProbability IM d mM hd hmM BM tM (ζ/2) hBM htM (by positivity)
  obtain ⟨NO,hO⟩:=mixed_ordinary_approximate_family_highProbability IO d hd mO hmO BO tO hBO htO (ζ/2) (by positivity)
  refine ⟨max NM NO,?_⟩
  intro V U _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ wM hwM gM jM wO hwO gO jO a μ
  have hm:=hM V U (by omega) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ wM hwM gM jM a
  have ho:=hO V U (by omega) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort wO hwO gO jO a
  let EM:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),mixedClassRetentionSpace true π d a ω)→Prop:=fun z=>∀ i root,
      |typedMarkedPotentialLoad (wM i) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gM i) (jM i)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wM i W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gM i) (jM i) a|<tM
  let EO:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),mixedClassRetentionSpace true π d a ω)→Prop:=fun z=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (wO i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (gO i) (jO i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then wO i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gO i) (jO i) (orderedOrdinaryResourceEmbedding a)|<tO i
  have hm':1-ζ/2≤(μ.sigma (mixedClassActualRetention true π d a)).probability EM:=hm
  have ho':1-ζ/2≤(μ.sigma (mixedClassActualRetention true π d a)).probability EO:=ho
  have hjoin:=finiteLaw_good_intersection (μ.sigma (mixedClassActualRetention true π d a)) EM EO (ζ/2) ho'
  change 1-ζ≤(μ.sigma (mixedClassActualRetention true π d a)).probability (fun z=>EM z ∧ EO z)
  linarith
end Oberwolfach
