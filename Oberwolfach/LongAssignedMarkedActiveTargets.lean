module

public import Oberwolfach.ExpandedMarkedSeedEventToTargets
public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongAssignedSeedTargets
public import Oberwolfach.LongRawHubContext

@[expose] public section
/-! Active marked targets for the original assigned seed on the actual
positive-mass expanded-and-retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_marked_named_seed_active_targets
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hd:2≤d) (hm:2≤m) (θ D p₁ k₁ u₀:ℝ)
    (hD:0<D) (hp₁:0≤p₁) (hk₁:0≤k₁) (hu₀:0≤u₀)
    (hp₂:0<(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)
    (hk₂:0<(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D)
    (hsum:2*p₁+2*k₁+2*((∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D)+
      2*((∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D)+u₀≤1)
    (hq:∀u g,0≤longAssignedIntervalProbability F hF K m θ u g)
    (hQ:∀u,∑g,longAssignedIntervalProbability F hF K m θ u g≤1/8)
    (hs:∀u j,0≤longAssignedSpokeProbability F hF K m θ u j)
    (hS:∀u,∑j,longAssignedSpokeProbability F hF K m θ u j≤
      intervalUncoveredProbability d (∑g,longAssignedIntervalProbability F hF K m θ u g))
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (g₀:Bool) (τ A B t:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight):
    let p₂:=(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D
    let k₂:=(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
    ∀(z:Σ ω:MixedClassRaw (V:=Fin n) (U:=U) true,mixedClassRetentionSpace true π d g₀ ω),
    0<((FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u₀
      hp₁ hk₁ hp₂.le hk₂.le hu₀ hsum d hd q hq hQ s hs hS)).sigma
      (mixedClassActualRetention true π d g₀)).mass z →
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let state:=longRawHubState P π d σ true true
    rawMarkedSeedConcentrated P π d m p₂ k₂ q s true true t
      (longAssignedMarkedSeed F hF K m d θ D π weight) σ →
    ∀root,state root=true→
      |resourcePatternLoad typedMarkedOccurrenceResources (longAssignedMarkedSeed F hF K m d θ D π weight)
        (fun _ _=>true) root state-longAssignedMixedTarget F hF K m θ D p₂ k₂ none root|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ none root :=by
  intro p₂ k₂ q s z hpos σ state hconc
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hspos:∀u,0<s u true:=by intro u;simpa [s,longAssignedSpokeProbability] using hb u
  have hbalance:∑u,q u true=D*k₂:=by
    dsimp [q,k₂,longAssignedIntervalProbability]
    field_simp
  have hh:=expanded_marked_seed_event_to_active_targets (V:=Fin n) (U:=U) P π d m hd hm
  have hdec : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n :=
    Subsingleton.elim _ _
  rw [hdec] at hh
  have hh:=hh p₁ k₁ p₂ k₂ u₀ hp₁ hk₁ hp₂ hk₂ hu₀ hsum q hq hQ s hs hS hnoshort
    g₀ true true D τ A B t hD hspos hbalance weight hw z hpos
  have hmixed:=hh hconc
  intro root hroot
  have h:=hmixed root hroot
  rw [long_assigned_marked_seed_target F hF K m θ D p₂ k₂ root] at h
  dsimp only [state,longRawHubState,longAssignedMarkedSeed,q,s,longAssignedSpokeProbability,p₂,k₂] at h ⊢
  convert h using 1 <;> congr 4 <;>
    first | rfl | exact Subsingleton.elim _ _ | (funext x; rfl)
end Oberwolfach
