module

public import Oberwolfach.ExpandedRawActiveMarkedSeedBounds
public import Oberwolfach.LongSeedEvents

@[expose] public section
/-! The marked root-omitted seed event gives the active marked target
estimates on the same positive-mass expanded-and-retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_marked_seed_event_to_active_targets
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hd:2≤d) (hm:2≤m)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0<p₂) (hk₂:0<k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (g₀ g j:Bool) (D τ A B t:ℝ) (hD:0<D)
    (hspos:∀u,0<s u j) (hbalance:∑u,q u g=D*k₂)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (z:Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂.le hk₂.le hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)).mass z):
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let H:=rawMarkedPairSpokes π d σ g j
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ _=>True) (fun _ _=>True)=>weight W.1.val/(D*p₂^m*k₂*(s W.2.val j)^m)
    rawMarkedSeedConcentrated P π d m p₂ k₂ q s g j t seed σ →
    ∀root,typedMarkedResourceState (rawMarkedPairRims P π d σ) H root=true →
      |resourcePatternLoad typedMarkedOccurrenceResources seed (fun _ _=>true) root
        (typedMarkedResourceState (rawMarkedPairRims P π d σ) H)-
        markedSeedRootTarget m p₂ k₂ q s g j root|≤
        t+τ*markedSeedRootTarget m p₂ k₂ q s g j root :=by
  intro σ H seed hE
  exact expanded_raw_marked_active_seed_bounds P π d m hd hm p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum
    q hq hQ s hs hS hnoshort g₀ g j D τ A B t hD hspos hbalance weight hw z hpos hE
end Oberwolfach
