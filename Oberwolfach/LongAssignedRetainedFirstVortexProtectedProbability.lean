module

public import Oberwolfach.LongAssignedRetainedProtectedProbability
public import Oberwolfach.LongFirstVortexReservedProtectedGraph

@[expose] public section
/-! The chosen first vortex set supplies the protected graph and its degree
budget in the assigned retained-class probability event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance assignedFirstVortexProtectedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
theorem long_assigned_retained_first_vortex_protected_probability
    (α ρ₀ rClass ξ δ θ:ℝ) (B K m d:ℕ)
    (hα:0<α) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1) (hrClass:0<rClass) (hξ:0<ξ) (hδ:0<δ)
    (hθ:0≤θ) (hθ1:θ≤1/100) (hK:0<K) (hm:7≤m) (hd:2≤d)
    (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ):
    ∃N:ℕ,∀n:ℕ,∀hn:max N 1≤n,∀(U I:Type) [Fintype U] [DecidableEq U] [Fintype I]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hclass:∀u,factorPreparationClass (F u) K=none)
    (density:I→ℝ) (i:I) (Dnat:ℕ) (hD:0<Dnat) (heven:Even Dnat)
    (hdensity:∀j,0≤density j) (hdensitySum:∑j,density j=1)
    (hsmall:∀j,density j=0 ∨ rClass≤density j)
    (hcurrent:rClass≤density i) (hρlo:ρ₀≤density i)
    (hsize:density i*Dnat=2*Fintype.card U)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hreg:P.IsRegularOfDegree Dnat) (hmin:(1/2+α)*n≤(Dnat:ℝ))
    (βQ εQ:ℝ) (vsize:ℕ) (Q:Vortex U P Dnat βQ εQ vsize) (hεQ:0≤εQ)
    (hεQcap:εQ≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32),
    let Z:=spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1)
    let ρ:=density i
    let D:ℝ:=Dnat
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    let hLaw:=long_assigned_actual_raw_law_parameters (by omega) F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
      hθ hθ1 hρ₀ hρlo (by have hh:=Finset.single_le_sum (fun j _=>hdensity j) (Finset.mem_univ i); simpa only [hdensitySum] using hh)
      (by change 0<(Dnat:ℝ); exact_mod_cast hD) hsize hcut hclass
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ udens
      hLaw.1 hLaw.2.1 hLaw.2.2.1 hLaw.2.2.2.1 hLaw.2.2.2.2.1 hLaw.2.2.2.2.2.1
      d hd q hLaw.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.1 s
      hLaw.2.2.2.2.2.2.2.2.1 hLaw.2.2.2.2.2.2.2.2.2)
    let f:=fun (ω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) e=>rawExpandedMarkedCollapse e (ω e)
    letI : Nonempty (Fin n):=⟨⟨0,by omega⟩⟩
    let ν:=fun raw:RawMarkedOutcome (Fin n) U Bool Bool=>
      startRetentionLaw (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)
        (startRetentionMinimum (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false)) (startRetentionMinimum_le _);
    1-δ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∃T:SimpleGraph (Fin n),T≤P ∧ T.IsRegularOfDegree (2*Fintype.card U) ∧
          (∀x y,(Z⊔A).Adj x y→(T.Adj x y↔(longPhysicalStateGraph P z.1 {0,1,2,3,4}).Adj x y)) ∧
          (∀v,((changed ((longPhysicalStateGraph P z.1 {0,1,2,3,4}).neighborFinset v) (T.neighborFinset v)).card:ℝ)≤ξ*n)) := by
  obtain ⟨N,hN⟩:=long_assigned_retained_protected_probability α ρ₀ rClass ξ δ θ B K m d
    hα hρ₀ hrClass hξ hδ hθ hθ1 hK hm hd hcut
  refine ⟨N,?_⟩
  intro n hn U I _ _ _ F hF Allowed hAllowed hclass density i Dnat hD heven hdensity hdensitySum hsmall hcurrent hρlo hsize P π hreg hmin βQ εQ vsize Q hεQ hεQcap Z
  obtain ⟨_,hProtect⟩:=long_first_vortex_reserved_protected_graph Q α ρ₀ hα.le hρ₀.le hρ₀1 hεQ hεQcap
  have hh:=hN n hn U I F hF Allowed hAllowed hclass density i Dnat hD heven hdensity hdensitySum hsmall hcurrent hρlo hsize P Z π hreg hmin hProtect
  have hdec6:assignedProtectedFinDecidable 6=assignedFirstVortexProtectedFin 6:=Subsingleton.elim _ _
  try rw [hdec6] at hh
  exact hh
end Oberwolfach
