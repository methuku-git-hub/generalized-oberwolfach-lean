module

public import Oberwolfach.OrdinaryAssignedReferenceBalanceColumns

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

theorem ordinary_assigned_reference_balance_columns_eventually
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
      (E z ∧ (∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\Fbad).degree v:ℝ)-
        2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)|≤σ*n+2*(σ*n)+LF)) ∧
      ∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)-rsv*n|<σ*n):=by
  obtain ⟨N,hN⟩:=ordinary_reference_concentration_tails_eventually_small d σ χ hσ hχ
  refine ⟨N,?_⟩
  intro n hn hn0 D K U _ _ hUn F hF P Fbad hP hD i₀ rsv θ c ρ₀ smin hρ₀ hρlo sampling π hnoshort LF hFbad R _ ν E εE p p₂ q s μ hE
  have hinputs:=ordinary_assigned_reference_original_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling
  have htail:=hN n hn (Fintype.card U) hinputs.1 hUn
  have ht:0<σ*(n:ℝ):=mul_pos hσ (by exact_mod_cast hn0)
  have hh:=ordinary_assigned_reference_balance_columns_on_prior F hF P Fbad hP hD i₀ rsv θ c ρ₀ smin d hd hρ₀ hρlo sampling π hnoshort hn0
    (σ*n) (σ*n) LF (σ*n) ht.le ht ht hFbad ν E εE hE
  have hcolour:0≤36*(n:ℝ)*Real.exp (-2*(σ*n)^2/n):=by positivity
  linarith
end Oberwolfach
