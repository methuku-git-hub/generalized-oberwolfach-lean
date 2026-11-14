module

public import Oberwolfach.OrdinaryThreeStepBalanceProductAt
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section
/-! Attach the lookback balance tests to any existing event in the actual
assigned sampling law, including a matching/correction and parent prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_lookback_balance_on_prior_split
    (n qCount D mv m K d mBalance:ℕ) (hd:2≤d)
    (βfreq ρ₀ θ εR εH β ε χ:ℝ) (hβfreq:0<βfreq) (hρ₀:0<ρ₀)
    (hbalanceAt:OrdinaryThreeStepBalanceProductAt d hd εR εH β ε ρ₀ χ mBalance)
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hn:0<n) (hhalf:(n:ℝ)/2≤D)
    (hρlo:ρ₀ ≤ initialIndexDensity (Fin qCount) D) (hρhi:initialIndexDensity (Fin qCount) D≤1) (hm:mBalance≤mv)
    (Q:VortexLookback (Fin qCount) P D β ε mv 2) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i)
    (hshort:∀x l,0<l→l<2*d+1→(π^l) x≠x):
    ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 (Fin n)→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop) (loss:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS);
    1-loss≤((μ.sigma ν).prod κcoins).probability E→
    1-(loss+χ)≤((μ.sigma ν).prod κcoins).probability (fun z=>E z ∧
      OrdinaryVortexThreeStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q.toVortex π hπ (2*p) rsv s false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      OrdinaryVortexThreeStepEditedBalanceEvent P D mv β ε rsv εR εH Q π hπ d false
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  intro R _ ν κcoins E loss p p₂ q s μ hE
  have hrsv:0≤rsv:=(show 0≤ρ₀*(βfreq/200) by positivity).trans sampling.hsmin
  have hpEq:2*p=initialIndexDensity (Fin qCount) D*rsv:=by dsimp [p];ring
  have hnF:0<Fintype.card (Fin n):=by simpa using hn
  have hhalfF:(Fintype.card (Fin n):ℝ)/2≤D:=by simpa using hhalf
  have hdecN:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
  have hstep:=hbalanceAt (Fin n) (Fin qCount) Bool Bool P (permutationConflictGraph π (3*d)) D mv
    hreg hnF hhalfF hρlo hρhi hm Q π hπ hshort le_rfl
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    q sampling.hq sampling.hQ s sampling.hs sampling.hS false rsv sampling.hfalse hrsv hpEq (R:=R)
  rw [hdecN] at hstep
  exact hstep ν κcoins E loss hE
end Oberwolfach
