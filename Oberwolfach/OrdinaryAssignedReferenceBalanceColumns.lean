module

public import Oberwolfach.OrdinaryAssignedReferenceOriginalInputs
public import Oberwolfach.OrdinaryPriorBalanceAndColumns
public import Oberwolfach.OrdinaryReferenceConcentrationTails

@[expose] public section
/-! On the assigned sampling law, derive the reference mean from the original
regular host and attach row balance and spoke-column bounds to any prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_reference_balance_columns_on_prior
    {n D K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P Fbad:SimpleGraph (Fin n)) (hP:P.IsRegularOfDegree D) (hD:0<D)
    (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hn:0<n)
    (tR tH LF tS:ℝ) (htR:0≤tR) (htH:0<tH) (htS:0<tS)
    (hFbad:∀v,(Fbad.degree v:ℝ)≤LF)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ):
    let p:=initialIndexDensity U D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let lossB:=2*(n:ℝ)*Real.exp (-2*tR^2/n)+
      (n:ℝ)*(2*Real.exp (-2*tH^2/((4*(d:ℝ)+3)^2*Fintype.card U)))
    let lossS:=4*(Fintype.card U:ℝ)*Real.exp (-2*tS^2/((4*(d:ℝ)+3)^2*n));
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+lossB)+lossS)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ (∀v,|(((rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)))\Fbad).degree v:ℝ)-
        2*((Finset.univ.filter (fun w=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)|≤tR+2*tH+LF)) ∧
      ∀w,|((Finset.univ.filter (fun v=>rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) false v w)).card:ℝ)-rsv*n|<tS):=by
  intro p p₂ q s μ lossB lossS hE
  obtain ⟨hU,hsize,hcentre,hspoke,hzero,hpmin,hsmin',hrsv⟩:=
    ordinary_assigned_reference_original_inputs F hF P hP hD K i₀ rsv θ c ρ₀ smin d hρ₀ hρlo sampling
  exact ordinary_prior_reference_balance_and_columns P Fbad π p 0 p₂ 0 sampling.u
    sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS
    hnoshort hn hU rsv tR tH LF tS htR htH htS hspoke hcentre hFbad ν E εE hE
end Oberwolfach
