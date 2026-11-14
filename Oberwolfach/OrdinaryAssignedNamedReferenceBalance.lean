module

public import Oberwolfach.OrdinaryReferenceNamedBalance

@[expose] public section
/-! The assigned-law reference balance and spoke columns may be added to any
prior at arbitrarily small fixed loss once the order is sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_named_reference_balance_eventually
    (d:ℕ) (hd:2≤d) (σ χ:ℝ) (hσ:0<σ) (hχ:0<χ):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀{D K:ℕ} {U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P Fbad:SimpleGraph (Fin n)),P.IsRegularOfDegree D→0<D→
    ∀(i₀:Fin K) (rsv θ c ρ₀ smin:ℝ),0<ρ₀→ρ₀≤ initialIndexDensity U D→
    ∀(sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d)
    (π:Equiv.Perm (Fin n)),(∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀LF:ℝ,(∀v,(Fbad.degree v:ℝ)≤LF)→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
    (E:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤(μ.sigma ν).probability (fun z=>
      E z ∧ OrdinaryReferenceBalanceColumnsEvent P Fbad π d rsv σ LF z.1):=by
  obtain ⟨N,hN⟩:=ordinary_assigned_reference_balance_columns_eventually d hd σ χ hσ hχ
  refine ⟨N,?_⟩
  intro n hn hn0 D K U _ _ hUn F hF P Fbad hP hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort LF hFbad R _ ν E εE p p₂ q s μ hE
  have hh:=hN n hn hn0 hUn F hF P Fbad hP hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort LF hFbad ν E εE hE
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.1.2,hz.2⟩
end Oberwolfach
