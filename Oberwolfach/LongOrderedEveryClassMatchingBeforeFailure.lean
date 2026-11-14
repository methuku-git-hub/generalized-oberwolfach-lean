module

public import Oberwolfach.LongMatchingOnlyClassTolerancesBeforeFailure
public import Oberwolfach.LongOrderedEveryClassProbability

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_ordered_every_class_matching_before_failure
    (K r d:ℕ) (hK3:3≤K) (hm:7≤(r+4)) (hd:2≤d)
    (θ ρ₀ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hBM:0<BM)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i) (αHost:ℝ) (hαHost:0<αHost)
    (alpha γ eps lam:ℝ) (heps:0<eps) (heps1:eps≤1) (hγε:γ≤eps) (hlam:0≤lam) (hlamθ:lam≤θ) (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (halpha:0<alpha) (halphaMass:alpha≤θ/(200*(K:ℝ)*(K:ℝ))) (hγ:0<γ):
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4:ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+(((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*((((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃lamEarly ηListEarly ζEarly:ℝ,0<lamEarly ∧ 0<ηListEarly ∧ 0<ζEarly ∧ ζEarly≤Δ ∧ ζEarly≤eps/8 ∧
    ∃NList:ℕ,
      (∀n≥NList,
        let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
        βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
        (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
        ∀(m:ℕ) (εQ:ℝ),εQ≤βList/32→1/(100*(m:ℝ))≤βList/16→
          βList/2+εQ+1/(100*(m:ℝ))+ηListEarly≤lamEarly) ∧
    ∃cOrient ξClass:ℝ,0<cOrient ∧ 0<ξClass ∧
      ξClass≤min (min (cOrient/4) ((ζEarly/4)/16)) (αHost*(ρ₀/200)^2/4) ∧
      ζEarly/2+ξClass+ζEarly/4≤ζEarly ∧
      LongEveryClassOrientationCap αHost ρ₀ (ζEarly/4) cOrient ∧
    ∀ (ε₀ ηEvent:ℝ),0≤ε₀→ε₀<1→0<ηEvent→∀B:ℕ,∃N:ℕ,∀n:ℕ,∀hn:max N 1≤n,∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (ρ D:ℝ) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin ((r+4)+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i,OrdinaryCycle P (ni i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(ni i))
    (huv:Fintype.card U≤n)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (εHost:ℝ)
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C:OrdinaryCycle P (ni i+2),if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤εHost*n)
    (hbudgetV:∀i∈longRetainedSeedIndices F hF K θ,
      6*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+εHost*n≤τ*D)
    (hbudgetE:∀i∈longRetainedSeedIndices F hF K θ,
      5*((ni i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ)
    (hτnonneg:0≤τ) (hτbound:τ≤τ₀)
    (Dnat vsize:ℕ) (β εQ:ℝ) (Q:Vortex U P Dnat β εQ vsize)
    (hεQ:0≤εQ) (hεQcap:εQ≤((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32)
    (htrim:1/(100*((r+4:ℕ):ℝ))≤((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16)
    (hDnat:(Dnat:ℝ)=D) (hreg:P.IsRegularOfDegree Dnat) (hmin:(1/2+αHost)*(n:ℝ)≤D)
    (γLoss σLoss:ℝ) (hγcap:γLoss≤ζEarly/2),
    let t:=t₀
    let tHub:=ξ*(n:ℝ)
    let b:=longAssignedApproxOrdinaryWeight F hF K (r+4) θ
    let a:=longAssignedApproxMarkedWeight F hF K (r+4) θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/((r+4:ℕ):ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/((r+4:ℕ):ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K (by omega) (r+4) d hm hd θ ρ₀ ρ D
      hθpos.le hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>
      rawExpandedMarkedCollapse e (ω e)
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4:ℕ):ℝ)+1))))
    let BMseed:=2*BM/pstar^(2*(r+4)+1)
    let BOseed:=fun i=>2*BO i/pstar^(2*(ni i+2))
    let Wm:=longAssignedMarkedSeed F hF K (r+4) d θ D π weight
    let Wo:=longAssignedOrdinarySeed F hF K (r+4) d θ D P π ni hni w
    let C:=10*((((r+4:ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed i)
    let ℓ:=fun i=>ni i+2
    let W:=longMixedSeedWeight Wm Wo
    let R:=longRawHubResources (U:=U) π d (r+4) ℓ
    let Pair:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>(((r+4:ℕ):ℝ)+1)^4*BMseed
      | some i=>((ni i:ℝ)+2)^3*BOseed i
    let Kpair:=1+(((r+4:ℕ):ℝ)+1)^4*BMseed+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed i
    let failure:=4*(Fintype.card U:ℝ)*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*(n:ℝ)))
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let Ret:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false))
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _)
    ∀(ExpandedGood:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,Ret (f ω))→Prop),
    1-ηEvent≤(μ.sigma (fun ω=>ν (f ω))).probability ExpandedGood →
    (∀z,ExpandedGood z→LongOrderedEveryClassSampleTests P π r K d θ ρ D F hF z)→
    1-(ε₀+6*ηEvent) ≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>ExpandedGood z ∧
      LongEveryClassValidDeletionEvent ζEarly P π d r γLoss σLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ D alpha γ eps
        ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w) := by
  obtain ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,
    lamEarly,ηListEarly,ζEarly,hlamEarly,hηList,hζ,hζΔ,hζeps,NList,hNumeric,
    cOrient,ξClass,hc,hξClass,hξbound,hsum,hCap,hOrdered⟩ :=
    long_matching_only_class_tolerances_before_failure K (r+4) d hK3 hm hd θ ρ₀ BM hθpos hθ hρ₀ hBM BO hBO αHost hαHost
      alpha γ eps lam heps heps1 hγε hlam hlamθ hepsAssign halpha halphaMass hγ
  refine ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,
    lamEarly,ηListEarly,ζEarly,hlamEarly,hηList,hζ,hζΔ,hζeps,NList,hNumeric,
    cOrient,ξClass,hc,hξClass,hξbound,hsum,hCap,?_⟩
  intro ε₀ ηEvent hε₀ hε₀lt hηEvent B
  obtain ⟨NEarly,hHost⟩ := hOrdered ε₀ ηEvent hε₀ hε₀lt hηEvent
  obtain ⟨NOrient,hNOrient,hOrient⟩:=long_ordered_every_class_probability αHost ρ₀ (ζEarly/4) cOrient hαHost hρ₀ hCap d B hd
  refine ⟨max (max NEarly NOrient) NList,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound Dnat vsize β εQ Q hεQ hεQcap htrim hDnat hreg hmin γLoss σLoss hγcap
  dsimp only
  intro ExpandedGood hExternal hTests
  have hnEarly:max NEarly 1≤n:=by omega
  have hprob:=hHost n hnEarly U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound ExpandedGood hExternal
  have hbudget:γLoss+ξClass+ζEarly/4≤ζEarly:=by linarith
  letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
  exact hOrient n (by omega) P Dnat vsize β εQ Q π r K θ ρ D F hF Allowed hAllowed weight w γLoss σLoss ξClass ζEarly alpha γ eps
    hεQ hεQcap hρlo hρ1 hD hθpos.le hθ hK3 hm hcut hclass hsize hDnat hreg hmin hξClass.le hξbound hbudget
    lamEarly ηListEarly hlamEarly.le hζ.le hηList.le (hNumeric n (by omega)) htrim _ ExpandedGood (1-(ε₀+6*ηEvent)) hTests hprob
end Oberwolfach
