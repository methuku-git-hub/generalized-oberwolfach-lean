module

public import Oberwolfach.OrdinaryRecodedMatchingBalanceSameSample
public import Oberwolfach.OrdinaryExpandedBoundaryOnPrior

@[expose] public section
/-! Keep recoded matching, reference balance and global interval boundaries
on the same assigned expanded sample and arbitrary dependent prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryBoundaryStartEvent {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):Prop :=
    ∀v,((rawIntervalBoundaryHubSet π d (fun e=>ω (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)

theorem ordinary_matching_balance_boundary_same_sample
    (d:ℕ) (hd:2≤d) (σ χbal χbd:ℝ) (hσ:0<σ) (hχbal:0<χbal) (hχbd:0<χbd):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀{D K:ℕ} {U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<D→
    ∀(i₀:Fin K) (rsv θ c ρ₀ smin:ℝ),0<ρ₀→ρ₀≤ initialIndexDensity U D→
    ∀(sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d)
    (π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
    (Core:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Prop)
    (a ζDel lamList:ℝ)
    (E:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop) (εM:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let Match:=OrdinaryRecodedMatchingExtra P π d θ c q s a ζDel lamList Core;
    1-εM≤(μ.sigma ν).probability (fun z=>E z ∧ Match z.1)→
    1-((εM+χbal)+χbd)≤(μ.sigma ν).probability (fun z=>
      ((E z ∧ Match z.1) ∧ OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
      OrdinaryBoundaryStartEvent π d z.1) :=by
  obtain ⟨Nbal,hbal⟩:=ordinary_recoded_matching_balance_same_sample d hd σ χbal hσ hχbal
  obtain ⟨Nbd,hbd⟩:=ordinary_expanded_boundary_on_prior d hd χbd hχbd
  refine ⟨max Nbal Nbd,?_⟩
  intro n hn hn0 D K U _ _ hUn F hF P hreg hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort R _ ν Core a ζDel lamList E εM p p₂ q s μ Match hMatch
  let Prior:=fun z=>(E z ∧ Match z.1) ∧
    OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1
  have hprior:1-(εM+χbal)≤(μ.sigma ν).probability Prior:=
    hbal n (by omega) hn0 hUn F hF P hreg hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort ν Core a ζDel lamList E εM hMatch
  have hU:0<Fintype.card U:=(ordinary_assigned_reference_original_inputs F hF P hreg hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling).1
  have hfinal:=hbd n (by omega) U hU hUn π p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    q sampling.hq sampling.hQ s sampling.hs sampling.hS hnoshort ν Prior (εM+χbal) hprior
  exact hfinal
end Oberwolfach
