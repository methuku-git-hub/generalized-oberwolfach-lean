module

public import Oberwolfach.LongAssignedSeedFunctionBounds
public import Oberwolfach.LongActualRawLawParameters
public import Oberwolfach.LongSeedEvents

@[expose] public section
/-! Joint concentration for the original assigned fixed weights under the
actual expanded law, with an arbitrary prior event on the same retained
experiment. This does not yet discharge the prior-event estimate or identify
all root expectations with the matching target profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_named_seed_common_event
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (ni:Fin K→ℕ) (hni:∀i,1≤ni i)
    (τ A BM:ℝ) (hBM:0<BM) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (g j:Bool) (t:ℝ) (ht:0<t)
    (Ret:RawMarkedOutcome (Fin n) U Bool Bool→Type) [∀a,Fintype (Ret a)]
    (ν:∀a,FiniteLaw (Ret a)):
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let hLaw:=long_assigned_actual_raw_law_parameters hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
      hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*m+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K m d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ D P π ni hni w
    ∀(Prior:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))→Prop)
      (ε:ℝ),
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability Prior →
    1-ε-mixedSeedFailureBound (Fin n) U d m K (fun i=>ni i+1) BMseed BOseed t≤
      (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>Prior z ∧
        rawMarkedSeedConcentrated P π d m p₂ k₂ q s g j t Wm
          (fun e=>rawExpandedApproximateCollapse e (z.1 e)) ∧
        ∀i,rawOrdinarySeedConcentrated P π d (ni i+2) p₂ k₂ q s g j t (Wo i)
          (fun e=>rawExpandedApproximateCollapse e (z.1 e))) :=by
  intro b a p₁ k₁ p₂ k₂ udens q s hLaw μ f pstar BMseed BOseed Wm Wo Prior ε hprior
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hbnd:=long_assigned_named_seed_bounds hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass P π ni hni τ A BM hBM weight hw hDlo hDhi BO hBO w hw0 hwupper
  have hM:∀W,0≤Wm W ∧ Wm W≤BMseed/(Fintype.card (Fin n):ℝ)^m :=by
    simpa only [Fintype.card_fin] using hbnd.2.2.1
  have hO:∀i W,0≤Wo i W ∧ Wo i W≤BOseed i/(Fintype.card (Fin n):ℝ)^(ni i+1) :=by
    simpa only [Fintype.card_fin] using hbnd.2.2.2
  have hcommon:=expanded_mixed_named_seed_event P π p₁ k₁ p₂ k₂ udens
    hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
    d m K hd (by omega) q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
    hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2
    hnoshort (by simpa only [Fintype.card_fin] using huv)
    (fun i=>ni i+1) (fun i=>by have:=hni i;omega) Wm Wo BMseed BOseed
    hbnd.1 hbnd.2.1 hM hO g j t ht Ret ν Prior ε
  have hdec : (fun a b : Fin n => Classical.propDecidable (a=b)) = instDecidableEqFin n :=
    Subsingleton.elim _ _
  rw [hdec] at hcommon
  have hcommon:=hcommon hprior
  convert hcommon using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
