module

public import Oberwolfach.OrdinaryBalancedMatchingReservoirEvent
public import Oberwolfach.OrdinaryExpandedDeepCoverEvent
public import Oberwolfach.OrdinaryAssignedProtectedReservoirHighProbability

@[expose] public section
/-! The assigned matching core and universal reservoir hold with high
probability on one expanded outcome and any dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedMatchingDeepReservoirCombinedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_balanced_matching_deep_cover_and_reservoir_high_probability
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hspacing:1/(4*(d:ℝ))≤5*θ^2/256) (ρ₀ BM t ξ ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (rRes:ℕ) (hrRes:3≤rRes) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ a:ℝ,0<a ∧ ∃ εabs εtrans εsample:ℝ,0<εabs ∧ 0<εtrans ∧ 0<εsample ∧
    ∀mRes:ℕ,∃aRes bRes tR:ℕ,1≤tR ∧ ∀tRes fRes:ℕ,∃N:ℕ,
    ∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→ω*n≤(Fintype.card U:ℝ)→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hcEq:c=(m:ℝ)+1) (hρlo:ρ₀≤ρ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p₁ k₁ k₂ u:ℝ) (hp₁:0≤p₁) (hk₁:0≤k₁) (hk₂:0≤k₂) (hu:0≤u)
    (γList pstarList βList lamList ζDel:ℝ) (hγList:0≤γList) (hpstarList:0≤pstarList)
    (hpstar: pstarList≤p₁) (hβList:0≤βList) (hlamList:0≤lamList) (hζDel:0≤ζDel)
    (hdegList:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (herrorList:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n)
    (hmarginList:βList*n+(n:ℝ)^(3/4:ℝ)≤(γList*pstarList^2)*n*(θ/2))
    (hbudgetList:(lamList+2*ζDel)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D;
    ∀(hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (hs:∀u j,0≤s u j) (hS:∀u,(∑ j,s u j) ≤ intervalUncoveredProbability d (∑g,q u g))
      (hp₂:0≤p₂) (hsum:2*p₁+2*k₁+2*p₂+2*k₂+u≤1)
      {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ)
      (mDeep KDeep:ℕ) (aDeep ρDeep θDeep εDeep:ℝ) (JDeep:Finset U)
      (Fbad:SimpleGraph (Fin n)) (tR tH:ℝ) (htR:0≤tR) (htH:0<tH),
    let Aref:=fun σ:RawWheelOutcome (Fin n) U Bool Bool=>
      OrdinaryUniformProtectedReservoirEvent rRes mRes tRes fRes aRes bRes εabs
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let wM:=fun (_:Unit)=>ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    (∀v,(2*p₁)*(P.degree v:ℝ)=2*(rsv*Fintype.card U)) →
    permutationConflictGraph π (3*d)≤Fbad →
    (∀v,(Fbad.degree v:ℝ)≤L) →
    (∀v,(cycleThreshold rRes+α)*n≤(P.degree v:ℝ)) →
    (∀v,|(P.degree v:ℝ)-D|≤εsample*n) →
    pmin≤2*p₁ → smin≤rsv →
    1-εDeep≤(FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>2*p₁)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability
      (OrdinaryDeepCoverEvent mDeep KDeep aDeep ρDeep θDeep P Fbad JDeep π d false) →
    1-εE≤(μ.sigma ν).probability E→
    let loss:=2*(n:ℝ)*Real.exp (-2*tR^2/n)+
      (n:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U)));
    1-((((εE+εDeep)+loss)+(1/(n:ℝ)+2/(n:ℝ)^2))+6*ζ)≤(μ.sigma ν).probability (fun z=>
      (((E z ∧ OrdinaryDeepCoverEvent mDeep KDeep aDeep ρDeep θDeep P Fbad JDeep π d false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧ (∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\Fbad).degree v:ℝ)-
        2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)|≤tR+2*tH+L)) ∧
        Aref (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      (∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
        IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lamList) ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧
      OrdinaryProtectedBadEdgeAssignments π d z.1 a) :=by
  obtain ⟨a,ha,εabs,εtrans,εsample,hεabs,hεtrans,hεsample,hFull⟩:=
    ordinary_assigned_balanced_matching_lists_and_reservoir_high_probability
      K d m hd hm θ hθ hθ1 hda hspacing ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO rRes hrRes α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  refine ⟨a,ha,εabs,εtrans,εsample,hεabs,hεtrans,hεsample,?_⟩
  intro mRes
  obtain ⟨aRes,bRes,tRes0,htRes0,hFull⟩:=hFull mRes
  refine ⟨aRes,bRes,tRes0,htRes0,?_⟩
  intro tRes fRes
  obtain ⟨N,hFull⟩:=hFull tRes fRes
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn hlo F hF hK i₀ rsv c ρ D hs0 hs1 hc hcEq hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu
    γList pstarList βList lamList ζDel hγList hpstarList hpstar hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList
    q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE mDeep KDeep aDeep ρDeep θDeep εDeep JDeep Fbad tR tH htR htH Aref μ wM wO hcentre hFbad hdeg hP hnear hp hRsv hDeep hE loss
  let Deep:RawWheelOutcome (Fin n) U Bool Bool→Prop:=OrdinaryDeepCoverEvent mDeep KDeep aDeep ρDeep θDeep P Fbad JDeep π d false
  let E':(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop:=
    fun z=>E z ∧ Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))
  have hJoined:=ordinary_expanded_add_deep_cover_event P Fbad π JDeep mDeep KDeep d hd aDeep ρDeep θDeep false
    p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum q hq hQ s hs hS ν E εE εDeep hDeep hE
  have hJoined':1-(εE+εDeep)≤(μ.sigma ν).probability E':=by exact hJoined
  exact hFull n hn hn0 U hUn hlo F hF hK i₀ rsv c ρ D hs0 hs1 hc hcEq hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu γList pstarList βList lamList ζDel hγList hpstarList hpstar hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList
    hq hQ hs hS hp₂ hsum ν E' (εE+εDeep) Fbad tR tH htR htH hcentre hFbad hdeg hP hnear hp hRsv hJoined'
end Oberwolfach
