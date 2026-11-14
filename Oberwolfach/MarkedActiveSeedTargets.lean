module

public import Oberwolfach.MarkedRetainedResourceState
public import Oberwolfach.RawMarkedTargetsFromConcentration

@[expose] public section
/-! The four concentration conclusions supply the marked seed target at
every resource retained in the actual sample, including zero densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedSeedRootTarget (m:ℕ) (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color):
    ((V×V)⊕(V×V))⊕(Bool×V×U)→ℝ
  | .inl (.inl _) => (m:ℝ)*k/p
  | .inl (.inr _) => 1
  | .inr (false,_,u) => (m:ℝ)*q u g/s u j
  | .inr (true,_,_) => 1

theorem marked_seed_targets_at_active_roots
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (p k:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _=>True) (fun _ _=>True)→ℝ) (t τ:ℝ)
    (hpos:∀v u,H true v u→q u g≠0)
    (hmarkedspoke:∀v u,q u g≠0→|typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ)
      (rawMarkedPairSpokes π d σ g j) (Sum.inr (true,v,u))-1|≤t+τ)
    (hordinaryspoke:∀v u,|typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ)
      (rawMarkedPairSpokes π d σ g j) (Sum.inr (false,v,u))-(m:ℝ)*q u g/s u j|≤t+τ*((m:ℝ)*q u g/s u j))
    (hmarkedrim:∀x y,¬PermutationClose π (3*d) x y→P.Adj x (π y)→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inr (x,y)))-1|≤t+τ)
    (hordinaryrim:∀x y,¬PermutationClose π (3*d) x y→P.Adj x y→
      |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inl (x,y)))-(m:ℝ)*k/p|≤t+τ*((m:ℝ)*k/p))
    (root:((V×V)⊕(V×V))⊕(Bool×V×U))
    (hactive:typedMarkedResourceState (rawMarkedPairRims P π d σ) H root=true):
    |typedMarkedPotentialLoad w (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      markedSeedRootTarget m p k q s g j root|≤t+τ*markedSeedRootTarget m p k q s g j root := by
  cases root with
  | inl e =>
    cases e with
    | inl xy =>
      rcases xy with ⟨x,y⟩
      have hr:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false x y=1 := by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using hactive
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) false x y).mp hr
      simpa [markedSeedRootTarget] using hordinaryrim x y hh.1 hh.2.1
    | inr xy =>
      rcases xy with ⟨x,y⟩
      have hr:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true x y=1 := by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using hactive
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) true x y).mp hr
      simpa [markedSeedRootTarget] using hmarkedrim x y hh.1 hh.2.1
  | inr a =>
    rcases a with ⟨b,v,u⟩
    cases b
    · simpa [markedSeedRootTarget] using hordinaryspoke v u
    · have hh:H true v u:=by simpa [typedMarkedResourceState] using hactive
      simpa [markedSeedRootTarget] using hmarkedspoke v u (hpos v u hh)
end Oberwolfach
