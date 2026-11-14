module

public import Oberwolfach.OrdinaryRecodedMatchingExtra
public import Oberwolfach.OrdinaryAssignedNamedReferenceBalance

@[expose] public section
/-! Attach reference balance and spoke-column control to the recoded matching
bundle on the exact same assigned expanded sample and arbitrary continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_recoded_matching_balance_same_sample
    (d:ℕ) (hd:2≤d) (σ χ:ℝ) (hσ:0<σ) (hχ:0<χ):
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
    1-(εM+χ)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ Match z.1) ∧ OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) :=by
  obtain ⟨N,hN⟩:=ordinary_assigned_named_reference_balance_eventually d hd σ χ hσ hχ
  refine ⟨N,?_⟩
  intro n hn hn0 D K U _ _ hUn F hF P hreg hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort R _ ν Core a ζDel lamList E εM p p₂ q s μ Match hMatch
  let Fbad:=permutationConflictGraph π (3*d)
  have hFbad:∀v,(Fbad.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  exact hN n hn hn0 hUn F hF P Fbad hreg hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort
    (2*((3*d:ℕ):ℝ)) hFbad ν (fun z=>E z ∧ Match z.1) εM hMatch
end Oberwolfach
