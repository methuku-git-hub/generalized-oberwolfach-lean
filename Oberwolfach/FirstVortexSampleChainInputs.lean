module

public import Oberwolfach.FirstVortexSelectedParentProbabilities
public import Oberwolfach.FirstVortexIncomingConcentrationProjection
public import Oberwolfach.LongUnassignedDensityBounds
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Assemble the exact sampling and concentration inputs used by the later
chain from one selected expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sampleChainInputsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) sampleChainInputsSix:DecidableEq (Fin 6):=instDecidableEqFin 6

theorem first_vortex_sample_chain_inputs
    {n K D:ℕ} [Nonempty (Fin n)] {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (hD:0<D)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ₀:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (z:MarkedExpandedActualOutcome (U:=U) π d):
    let m:ℝ:=(r+4:ℕ)
    let ρ:=initialIndexDensity U D
    let s₀:ℝ:=1/100
    let tstar:ℝ:=1/(200*m)
    let pstar:ℝ:=ρ₀/(800*m)
    let p:ℝ:=ρ*s₀/2
    let k:ℝ:=p/m
    let q:=longAssignedIntervalProbability F hF K (r+4) θ
    let s:=longAssignedSpokeProbability F hF K (r+4) θ
    let p₂:ℝ:=(∑w,longAssignedApproxOrdinaryWeight F hF K (r+4) θ w)/(D:ℝ)
    let k₂:ℝ:=(∑w,longAssignedApproxMarkedWeight F hF K (r+4) θ w)/(D:ℝ)
    let u:ℝ:=2*(∑w,(1-1/100-(1/100)/m-longAssignedApproxMarkedWeight F hF K (r+4) θ w-
      longAssignedApproxOrdinaryWeight F hF K (r+4) θ w))/(D:ℝ)
    let σ:=fun e:Sym2 (Fin n)=>z.1 (Sum.inl e);
    (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀(j:Fin 6) (v:Fin n),
      |((∑x,sampledColourOrientation P σ j v x:ℕ):ℝ)-markedExpandedPhysicalProbability p (ρ*(s₀/m)/2) p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p (ρ*(s₀/m)/2) p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ) ∧
      |(sampledColourDegree P (fun e=>(σ e).1) j v:ℝ)-markedExpandedPhysicalProbability p (ρ*(s₀/m)/2) p₂ k₂ u j*P.degree v|<(n:ℝ)^(3/5:ℝ))→
    k=ρ*(s₀/m)/2 ∧ (∀w,q w false=s₀/m) ∧ (∀w,s w false=s₀) ∧
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ pstar≤s₀ ∧ p≤1 ∧ k≤1 ∧ s₀≤1 ∧
    0<tstar ∧ tstar≤s₀/m ∧ pstar≤ρ*(s₀/m)/2 ∧
    ρ₀/400≤ρ*m*tstar/2 ∧ pstar≤ρ*m*tstar/2 ∧ pstar≤ρ*tstar/2 ∧ pstar≤tstar ∧
    (∀v,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false v).card:ℝ)-(∑w,q w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀j v,|((∑x,sampledColourOrientation P σ j x v:ℕ):ℝ)-markedExpandedPhysicalProbability p k p₂ k₂ u j/2*P.degree v|<(n:ℝ)^(3/5:ℝ)) ∧
    0≤u ∧ u≤2*θ ∧
    (∀v,|(sampledColourDegree P (fun e=>(σ e).1) 4 v:ℝ)-u*(P.degree v:ℝ)|≤(n:ℝ)^(3/5:ℝ)) :=by
  intro m ρ s₀ tstar pstar p k q s p₂ k₂ u σ hStart hOrient
  have hkEq:k=ρ*(s₀/m)/2:=by dsimp [k,p];ring
  have hnum:=first_vortex_selected_parent_probabilities (K:=K) F hF r θ ρ₀ ρ hρ₀ hρlo hρhi
  have hu:=long_unassigned_density_bounds hn hK (show 0<r+4 by omega) hD F hF θ hθ hθ1 hρhi
  have horient:=first_vortex_incoming_concentration_projection P σ p (ρ*(s₀/m)/2) p₂ k₂ u hOrient
  rw [←hkEq] at horient
  exact ⟨hkEq,hnum.1,hnum.2.1,hnum.2.2.1,hnum.2.2.2.1,hnum.2.2.2.2.1,hnum.2.2.2.2.2.1,
    hnum.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.2.2.1,
    hnum.2.2.2.2.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.2.2.2.2.1,
    hnum.2.2.2.2.2.2.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hnum.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,hnum.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    hStart,horient.1,hu.1,hu.2,horient.2⟩
end Oberwolfach
