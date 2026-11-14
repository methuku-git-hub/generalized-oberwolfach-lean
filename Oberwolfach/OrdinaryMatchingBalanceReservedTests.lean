module

public import Oberwolfach.OrdinaryMatchingBalanceBoundary
public import Oberwolfach.OrdinaryReservedCompletionOnPrior

@[expose] public section
/-! On the assigned sample, retain matching, reference balance, boundaries
and the manuscript's selected reserved-completion tests together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_balance_reserved_tests_same_sample
    (d:ℕ) (hd:2≤d) (smin σ χbal χbd χnbr χpair χpath:ℝ)
    (hsmin:0<smin) (hσ:0<σ) (hχbal:0<χbal) (hχbd:0<χbd) (hχnbr:0<χnbr) (hχpair:0<χpair) (hχpath:0<χpath):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀{D K:ℕ} {U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<D→
    ∀(i₀:Fin K) (rsv θ c ρ₀:ℝ),0<ρ₀→smin≤rsv→ρ₀ ≤ initialIndexDensity U D→
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
    1-(((((εM+χbal)+χbd)+χnbr)+χpair)+χpath)≤(μ.sigma ν).probability (fun z=>
      (((E z ∧ Match z.1) ∧ OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
        OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) :=by
  obtain ⟨Nb,hb⟩:=ordinary_matching_balance_boundary_same_sample d hd σ χbal χbd hσ hχbal hχbd
  obtain ⟨Nr,hr⟩:=ordinary_reserved_completion_tests_on_prior d hd smin χnbr χpair χpath hsmin.le hχnbr hχpair hχpath
  refine ⟨max Nb Nr,?_⟩
  intro n hn hn0 D K U _ _ hUn F hF P hreg hD i₀ rsv θ c ρ₀ hρ₀ hslo hρlo sampling π hnoshort R _ ν Core a ζDel lamList E εM p p₂ q s μ Match hM
  let Prior:=fun z=>((E z ∧ Match z.1) ∧ OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
    OrdinaryBoundaryStartEvent π d z.1
  have hp:1-((εM+χbal)+χbd)≤(μ.sigma ν).probability Prior:=
    hb n (by omega) hn0 hUn F hF P hreg hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort ν Core a ζDel lamList E εM hM
  have hU:0<Fintype.card U:=(ordinary_assigned_reference_original_inputs F hF P hreg hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling).1
  have hs:∀w,smin≤s w false:=by
    intro w
    simpa only [s,sampling.hfalse w] using hslo
  exact hr n (by omega) U hU hUn P π p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    q sampling.hq sampling.hQ s sampling.hs sampling.hS hnoshort hs ν Prior ((εM+χbal)+χbd) hp
end Oberwolfach
