module

public import Oberwolfach.ExpandedMarkedFiniteFamily
public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! The fixed marked wheel weights have simultaneous potential-load estimates
on the actual mixed experiment after conditional retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_marked_approximate_family_highProbability
    (I:Type) [Fintype I] (d m:ℕ) (hd:2≤d) (hm:3≤m) (B t ζ:ℝ) (hB:0<B) (ht:0<t) (hζ:0<ζ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (H₀ Hₖ:V→U→Prop)
    (w:∀ i:I,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B/(Fintype.card V:ℝ)^m)
    (g:I→Bool) (j:I→Bool)
    (a:Bool),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-ζ≤(μ.sigma (mixedClassActualRetention true π d a)).probability (fun z=>∀ i root,
      |typedMarkedPotentialLoad (w i) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (g i) (j i)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w i W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) a|<t):=by
  obtain ⟨N,hN⟩:=raw_expanded_marked_finite_family_highProbability I d m hd hm B t ζ hB ht hζ
  refine ⟨N,?_⟩
  intro V U _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ w hw g j a μ
  let F:=fun σ:RawMarkedOutcome V U Bool Bool=>
    StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a))
  let ν:=fun σ:RawMarkedOutcome V U Bool Bool=>
    startRetentionLaw (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)
      (startRetentionMinimum (rawStartHubSet π d (fun e=>σ (Sum.inr e)) a)) (startRetentionMinimum_le _)
  have hh:=hN V U Bool Bool hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ w hw g j F ν
  exact hh
end Oberwolfach
