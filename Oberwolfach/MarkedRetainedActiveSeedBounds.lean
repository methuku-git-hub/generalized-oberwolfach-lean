module

public import Oberwolfach.MarkedActiveSeedTargets
public import Oberwolfach.RetainedMarkedSeedStability
public import Oberwolfach.RetainedMarkedPositiveSupport
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! From the actual common expanded outcome, the original concentrated
marked seed bounds pass through start retention at every retained root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_retained_marked_active_seed_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hd:2≤d) (hm:3≤m)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0<p₂) (hk₂:0<k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (g₀ g j:Bool) (D τ A B t Bseed ζ:ℝ) (hD:0<D) (hBseed:0≤Bseed) (hζ:0≤ζ)
    (hspos:∀u,0<s u j) (hbalance:∑u,q u g=D*k₂)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (z:Σ ω:MixedClassRaw (V:=V) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω)
    (hpos:0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂.le hk₂.le hu₀ hsum d hd q hq hQ s hs hS)).sigma
        (mixedClassActualRetention true π d g₀)).mass z)
    (hu:Fintype.card U≤Fintype.card V):
    let σ:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g₀
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀)) z.2 g j
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ _=>True) (fun _ _=>True)=>weight W.1.val/(D*p₂^m*k₂*(s W.2.val j)^m)
    (∀W,0≤seed W ∧ seed W≤Bseed/(Fintype.card V:ℝ)^m) →
    RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g₀
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g₀))
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2 →
    (∀root,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      ∑W,(if root∈typedMarkedOccurrenceResources W then seed W else 0)*
        ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j a|<t) →
    ∀root,typedMarkedResourceState (rawMarkedPairRims P π d σ) H root=true →
      |resourcePatternLoad typedMarkedOccurrenceResources seed (fun _ _=>true) root
        (typedMarkedResourceState (rawMarkedPairRims P π d σ) H)-
        markedSeedRootTarget m p₂ k₂ q s g j root|≤
        (t+11*((m:ℝ)+1)^4*Bseed*ζ)+τ*markedSeedRootTarget m p₂ k₂ q s g j root := by
  intro σ H seed hseed good hconc root hactive
  have hn:0<Fintype.card V:=Fintype.card_pos
  have hpair:2*p₂+2*k₂≤1:=by linarith
  have htarg:=raw_marked_all_targets_from_concentration P π p₂ k₂ hp₂ hk₂ hpair d hd q hq hQ s hs hS
    hnoshort m (by omega) g j D τ A B t hD hspos hbalance weight hw σ hconc
  have hpositive:∀v u,H true v u→q u g≠0 := by
    intro v u hh
    exact ne_of_gt (expanded_retained_marked_spoke_positive_density π d hd g₀
      p k p₂ k₂ u₀ hp hk hp₂.le hk₂.le hu₀ hsum q hq hQ s hs hS z hpos g j v u hh)
  have hraw:=marked_seed_targets_at_active_roots P π d m p₂ k₂ q s g j σ H seed t τ hpositive
    (fun v u hp=>(htarg.1 v u hp).le) (fun v u=>(htarg.2.1 v u).le)
    (fun x y hc ha=>(htarg.2.2.1 x y hc ha).le) (fun x y hc ha=>(htarg.2.2.2 x y hc ha).le)
    root hactive
  have hstab:=retained_marked_seed_load_stability (π:=π) (b:=3*d) hm hn hu seed Bseed ζ hBseed hζ hseed
    (rawMarkedPairRims P π d σ) d (fun e=>z.1 (Sum.inr e)) g₀ _ z.2 good g j root
  have hstab' : |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-
      typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root|≤
        11*((m:ℝ)+1)^4*Bseed*ζ := by
    simpa [H,σ,rawMarkedPairSpokes,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse] using hstab
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
  have htri:=abs_add_le
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-
      typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root)
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      markedSeedRootTarget m p₂ k₂ q s g j root)
  have heq:typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-
      markedSeedRootTarget m p₂ k₂ q s g j root =
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-
      typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root)+
    (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      markedSeedRootTarget m p₂ k₂ q s g j root):=by ring
  rw [heq]
  linarith
end Oberwolfach
