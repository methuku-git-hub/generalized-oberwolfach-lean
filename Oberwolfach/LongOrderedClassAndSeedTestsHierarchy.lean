module

public import Oberwolfach.LongAssignedResidualSeedTestsEarly
public import Oberwolfach.LongOrderedEveryClassLateDeletionCap
public import Oberwolfach.LongOrderedEveryClassUniformMatchingClassCap
public import Oberwolfach.LongMatchingFixedSpacingParameters

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_ordered_class_and_seed_tests_hierarchy
    (K r d:ℕ) (hK3:3≤K) (hm:7≤(r+4)) (hd:2≤d)
    (θ ρ₀ BM:ℝ) (hθpos:0<θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hBM:0<BM)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i) (αHost:ℝ) (hαHost:0<αHost)
    (lam:ℝ) (hlam:0<lam) (hlamθ:lam≤θ) (ξCap:ℝ) (hξCap:0<ξCap):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let hpadded:=@long_padded_seed_length_eq_exponent K
    let pstar₀:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*(((r+4:ℕ):ℝ)+1))))
    let BMseed₀:=2*BM/pstar₀^(2*(r+4)+1)
    let BOseed₀:=fun i=>2*BO i/pstar₀^(2*(ni i+2))
    let Kpair₀:=1+(((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^3*BOseed₀ i
    let C₀:=10*((((r+4:ℕ):ℝ)+1)^4*BMseed₀+∑i:Fin K,((ni i:ℝ)+2)^4*BOseed₀ i)
    ∃ηSeed:ℝ,0<ηSeed ∧ ∃tSeed τSeed ΔSeed ξSeed:ℝ,0<tSeed ∧ 0<τSeed ∧ τSeed≤1/16 ∧ 0<ΔSeed ∧ 0<ξSeed ∧ 4*ξSeed≤eps/2 ∧
    ∃η:ℝ,0<η ∧ ∃t₀ τ₀ Δ ξ:ℝ,0<t₀ ∧ 0<τ₀ ∧ τ₀≤1/16 ∧ 0<Δ ∧ 0<ξ ∧ 4*ξ≤eps/2 ∧
    ∃lamEarly ηListEarly ζEarly:ℝ,0<lamEarly ∧ 0<ηListEarly ∧ 0<ζEarly ∧ ζEarly≤Δ ∧ ζEarly≤eps/8 ∧ ζEarly≤ΔSeed ∧
    ∃NList:ℕ,
      (∀n≥NList,
        let βList:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
        (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
        βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*(1/100:ℝ) ∧
        (lamEarly+2*ζEarly)*n≤βList*n ∧ (n:ℝ)^(3/4:ℝ)≤ηListEarly*n ∧
        ∀(m:ℕ) (εQ:ℝ),εQ≤βList/32→1/(100*(m:ℝ))≤βList/16→
          βList/2+εQ+1/(100*(m:ℝ))+ηListEarly≤lamEarly) ∧
    ∃cOrient ξClass:ℝ,0<cOrient ∧ 0<ξClass ∧ ξClass≤ξCap ∧
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
    (hτnonneg:0≤τ) (hτbound:τ≤min τSeed τ₀)
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
    1-(ε₀+36*ηEvent) ≤
    (μ.sigma (fun ω=>ν (f ω))).probability (fun z=>ExpandedGood z ∧
      (∀u,|(((ordinaryCommonHubSpokeRoots u).filter (fun root=>
        longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true)).card:ℝ)-
        longAssignedApproxOrdinaryWeight F hF K (r+4) θ u*n|≤ξSeed*n) ∧
      (∀i root,longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true root=true→
        |resourcePatternLoad (longRawHubResources (U:=U) π d (r+4) (fun i=>ni i+2) i)
          (longMixedSeedWeight Wm Wo i) (fun _ _=>true) root
          (longRawHubState P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) true true)-
          longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root|≤
        tSeed+τ*longAssignedMixedTarget F hF K (r+4) θ D p₂ k₂ i root) ∧
      (∀(Del:SimpleGraph (Fin n)) (δ:ℝ), (∀x,(Del.degree x:ℝ)≤δ)→
        δ≤ΔSeed*n→0≤tSeed+C*(δ/(n:ℝ))+4*τ ∧ tSeed+C*(δ/(n:ℝ))+4*τ≤eps/2) ∧
      LongEveryClassValidDeletionEvent ζEarly P π d r γLoss σLoss ξClass z
        (Q.extendedVertices 1) (Q.extendedIndices 1) K B θ D alpha γ eps
        ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) F hF weight w ∧
      ∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤ζEarly*n)→
        LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps ζEarly
          ((min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16) P π F hF weight w z (Q.extendedVertices 1) Del) := by
  obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε⟩ :=
    long_matching_fixed_spacing_parameters K d (by omega) (by omega) θ lam hθpos hlam
  refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,?_⟩
  have halphaMass':min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))≤θ/(200*(K:ℝ)*(K:ℝ)):=by simpa only [pow_two,mul_assoc] using halphaMass
  obtain ⟨ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedCap,hΔSeed,hξSeed,hξSeedEps,hSeed⟩:=
    long_assigned_residual_seed_tests_before_failure K (r+4) d hK3 hm hd θ ρ₀ BM hθpos hθ hρ₀ hBM BO hBO
      _ _ eps lam heps heps1 hγε hlam.le hlamθ hepsAssign halpha halphaMass' hγ
  refine ⟨ηSeed,hηSeed,tSeed,τSeed,ΔSeed,ξSeed,htSeed,hτSeed,hτSeedCap,hΔSeed,hξSeed,hξSeedEps,?_⟩
  obtain ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,hCapChoice⟩:=
    long_ordered_every_class_uniform_matching_with_late_deletion_cap K r d hK3 hm hd θ ρ₀ BM hθpos hθ hρ₀ hBM BO hBO αHost hαHost
      _ _ eps lam heps heps1 hγε hlam.le hlamθ hepsAssign halpha halphaMass' hγ ξCap hξCap
  obtain ⟨lamEarly,ηListEarly,ζEarly,hlamEarly,hηList,hζ,hζΔ,hζeps,hζSeed,NList,hNumeric,
    cOrient,ξClass,hc,hξClass,hξClassCap,hξbound,hsum,hCap,hClass⟩:=hCapChoice ΔSeed hΔSeed
  refine ⟨η,hη,t₀,τ₀,Δ,ξ,ht₀,hτ₀,hτhalf,hΔ,hξ,hξeps,
    lamEarly,ηListEarly,ζEarly,hlamEarly,hηList,hζ,hζΔ,hζeps,hζSeed,NList,hNumeric,
    cOrient,ξClass,hc,hξClass,hξClassCap,hξbound,hsum,hCap,?_⟩
  intro ε₀ ηEvent hε₀ hε₀lt hηEvent B
  obtain ⟨NSeed,hSeedHost⟩:=hSeed 0 ηEvent (by norm_num) (by norm_num) hηEvent
  obtain ⟨NClass,hClassHost⟩:=hClass ε₀ (6*ηEvent) hε₀ hε₀lt (by positivity) B
  refine ⟨max NSeed NClass,?_⟩
  intro n hn U _ _ F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg hτbound Dnat vsize β εQ Q hεQ hεQcap htrim hDnat hreg hmin γLoss σLoss hγcap
  dsimp only
  intro ExpandedGood hExternal hTests
  have hSeedProb:=hSeedHost n (by omega) U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg (hτbound.trans (min_le_left _ _)) ExpandedGood hExternal
  have hSeedReady:=hSeedProb
  rw [zero_add] at hSeedReady
  have hClassProb:=hClassHost n (by omega) U F hF Allowed hAllowed ρ D hρlo hρ1 hD hsize hcut hclass P π τ A weight hw hDlo hDhi w hw0 hwupper huv hnoshort εHost he hdeg hbudgetV hbudgetE hτnonneg (hτbound.trans (min_le_right _ _)) Dnat vsize β εQ Q hεQ hεQcap htrim hDnat hreg hmin γLoss σLoss hγcap
    _ hSeedReady (by intro z hz;exact hTests z hz.1)
  have hLoss:(1:ℝ)-(ε₀+6*(6*ηEvent))=1-(ε₀+36*ηEvent):=by ring
  rw [hLoss] at hClassProb
  apply le_trans hClassProb
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1.1,hz.1.2.1,?_,?_,hz.2.1,hz.2.2⟩
  · intro i root hroot
    have hh:=hz.1.2.2.1 i root hroot
    simpa only [Nat.cast_add,Nat.cast_ofNat,one_div] using hh
  · intro Del δ hDel hδ
    have hh:=hz.1.2.2.2 Del δ hDel hδ
    simpa only [Nat.cast_add,Nat.cast_ofNat,one_div] using hh
end Oberwolfach
