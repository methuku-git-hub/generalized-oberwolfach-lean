module

public import Oberwolfach.LongAssignedMarkedActiveTargets
public import Oberwolfach.LongAssignedOrdinaryActiveTargets
public import Oberwolfach.LongMixedInputsFromRetained
public import Oberwolfach.LongRawHubContext

@[expose] public section
/-! The original marked and ordinary assigned seeds have the mixed target
loads on the same positive-mass retained outcome, assuming the original
fractional-cycle, host-degree and numerical inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_actual_mixed_active_loads
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m d:ℕ) (hd:2≤d) (hm:2≤m) (θ D p₁ k₁ u₀:ℝ)
    (hθ0:0≤θ) (hθ1:θ≤1) (hD:0<D) (hp₁:0≤p₁) (hk₁:0≤k₁) (hu₀:0≤u₀)
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
    (g₀:Bool) (τ A BM t ε:ℝ) (ht:0≤t) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (BO:Fin K→ℝ)
    (hBO:∀i,0≤BO i) (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+ε*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ):
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
    let ℓ:=fun i=>ni i+2
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d m ℓ
    rawMarkedSeedConcentrated P π d m p₂ k₂ q s true true t Wm σ →
    (∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s true true t (Wo i) σ) →
    ∀i root,state root=true→
      |resourcePatternLoad (R i) (W i) (fun _ _=>true) root state-
        longAssignedMixedTarget F hF K m θ D p₂ k₂ i root|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p₂ k₂ i root :=by
  intro p₂ k₂ q s z hpos σ state ℓ Wm Wo W R hM hO
  letI : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  have hMtarget:=long_assigned_marked_named_seed_active_targets hn F hF K m d hd hm θ D p₁ k₁ u₀
    hD hp₁ hk₁ hu₀ hp₂ hk₂ hsum hq hQ hs hS hb P π hnoshort g₀ τ A BM t weight hw z hpos hM
  let hub:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2)→U:=fun _ W=>W.2
  let base:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2)→ℝ:=fun i W=>
    physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hni i) (w i) W.1.val/
      (((ni i+2:ℕ):ℝ)*D*p₂^(ni i+2)*(longAssignedApproxOrdinaryWeight F hF K m θ W.2)^(ni i+1))
  have hseed:∀i W,Wo i W=(longAssignedKeptOrdinaryContribution F hF K θ i (hub i W)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub i W))*base i W:=by
    intro i W
    dsimp [Wo,longAssignedOrdinarySeed,hub,base,p₂]
    ring
  have hOtarget:∀i∈longRetainedSeedIndices F hF K θ,∀root,
      state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad orderedOrdinaryResources (Wo i) (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        ordinarySeedRootTarget D p₂ θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p₂ θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root:=by
    intro i hi
    have hh:=long_assigned_ordinary_named_seed_active_targets hn F hF K m d hd θ D k₂ hθ0 hθ1 hD
      P π ni hni w i (BO i) τ ε t (hBO i) (hw0 i) (hwupper i) (he i hi) hdeg
      (hbudgetV i hi) (hbudgetE i hi) hk₂.le hb hp₂ (by linarith) hq hQ hs hS hnoshort σ (hO i)
    exact hh
  have hmix:=long_mixed_active_inputs_from_retained F hF m θ D p₂ k₂ t τ ht
    typedMarkedOccurrenceResources (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (ni i+2))=>orderedOrdinaryResources W)
    Wm hub base state
  have hm:∀root,state root=true→
      |resourcePatternLoad typedMarkedOccurrenceResources Wm (fun _ _=>true) root state-
        markedSeedRootTarget m p₂ k₂ q s true true root|≤
        t+τ*markedSeedRootTarget m p₂ k₂ q s true true root:=by
    intro root hroot
    have h:=hMtarget root hroot
    rw [long_assigned_marked_seed_target F hF K m θ D p₂ k₂ root]
    exact h
  have ho:∀i∈longRetainedSeedIndices F hF K θ,∀root,
      state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad orderedOrdinaryResources (fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub i c)/
        longAssignedApproxOrdinaryWeight F hF K m θ (hub i c))*base i c) (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-
        ordinarySeedRootTarget D p₂ θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p₂ θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/longAssignedApproxOrdinaryWeight F hF K m θ u) root:=by
    intro i hi root hroot
    have h:=hOtarget i hi root hroot
    have hwEq:Wo i=(fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub i c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub i c))*base i c):=funext (hseed i)
    rw [←hwEq]
    exact h
  have hdec : (fun a b : U => Classical.propDecidable (a=b)) = (inferInstance : DecidableEq U) :=
    Subsingleton.elim _ _
  rw [hdec] at hmix
  have hall:=hmix hm ho
  have hfun:Wo=(fun i c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub i c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub i c))*base i c):=by
    funext i c
    exact hseed i c
  intro i root hroot
  have hh:=hall i root ((mem_bernoulliVertexSet state root).mpr hroot)
  rw [←hfun] at hh
  dsimp only [R,longRawHubResources,longRawSeedResources,W] at ⊢
  convert hh using 1 <;> congr 4 <;> first | rfl | exact Subsingleton.elim _ _ | (funext x; congr 4 <;> exact Subsingleton.elim _ _)
end Oberwolfach
