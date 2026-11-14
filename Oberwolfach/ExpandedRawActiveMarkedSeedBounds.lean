module

public import Oberwolfach.MarkedActiveSeedTargets
public import Oberwolfach.ExpandedRawMarkedPositiveSupport
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! On the original approximate-layer outcome, the concentrated marked
seed bounds hold at every active raw approximate resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_raw_marked_active_seed_bounds
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
        (mixedClassActualRetention true π d g₀)).mass z)
:
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let H:=rawMarkedPairSpokes π d σ g j
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ _=>True) (fun _ _=>True)=>weight W.1.val/(D*p₂^m*k₂*(s W.2.val j)^m)
    (∀root,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      ∑W,(if root∈typedMarkedOccurrenceResources W then seed W else 0)*
        ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j a|<t) →
    ∀root,typedMarkedResourceState (rawMarkedPairRims P π d σ) H root=true →
      |resourcePatternLoad typedMarkedOccurrenceResources seed (fun _ _=>true) root
        (typedMarkedResourceState (rawMarkedPairRims P π d σ) H)-
        markedSeedRootTarget m p₂ k₂ q s g j root|≤
        t+τ*markedSeedRootTarget m p₂ k₂ q s g j root := by
  intro σ H seed hconc root hactive
  have hpair:2*p₂+2*k₂≤1:=by linarith
  have htarg:=raw_marked_all_targets_from_concentration P π p₂ k₂ hp₂ hk₂ hpair d hd q hq hQ s hs hS
    hnoshort m (by omega) g j D τ A B t hD hspos hbalance weight hw σ hconc
  have hpositive:∀v u,H true v u→q u g≠0 := by
    intro v u hh
    exact ne_of_gt (expanded_raw_marked_spoke_positive_density π d hd g₀
      p k p₂ k₂ u₀ hp hk hp₂.le hk₂.le hu₀ hsum q hq hQ s hs hS z hpos g j v u (by
        simpa [H,σ,rawMarkedPairSpokes,rawExpandedApproximateCollapse] using hh))
  have hraw:=marked_seed_targets_at_active_roots P π d m p₂ k₂ q s g j σ H seed t τ hpositive
    (fun v u hp=>(htarg.1 v u hp).le) (fun v u=>(htarg.2.1 v u).le)
    (fun x y hc ha=>(htarg.2.2.1 x y hc ha).le) (fun x y hc ha=>(htarg.2.2.2 x y hc ha).le)
    root hactive
  have hpattern : resourcePatternLoad typedMarkedOccurrenceResources seed (fun _ _=>true) root
      (typedMarkedResourceState (rawMarkedPairRims P π d σ) H) =
        typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root := by
    unfold typedMarkedPotentialLoad resourceRootOmittedLoad resourcePatternLoad
    symm
    apply Finset.sum_congr rfl
    intro W _
    rw [patternValue_indicator]
    simp only [typedMarkedResourceState,decide_eq_true_eq,Finset.mem_sdiff,Finset.mem_singleton]
    have heq : (∀ f,f∈typedMarkedOccurrenceResources W ∧ f≠root →
        Sum.elim (rawMarkedPairRims P π d σ) (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) f) ↔
        (∀ f∈typedMarkedOccurrenceResources W,f≠root →
          Sum.elim (rawMarkedPairRims P π d σ) (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2) f) := by aesop
    simp only [heq]
    split_ifs <;> simp_all
  rw [hpattern]
  exact hraw
end Oberwolfach
