module

public import Oberwolfach.OrdinaryAssignedSamplingWitness
public import Oberwolfach.OrdinaryAssignedNamedSeeds

@[expose] public section
/-! The assigned sample recipe realizes the named approximate probability
    and all categorical-law hypotheses from the original factor assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_named_sampling_witness {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀) :
    ∃ u:ℝ, 0≤u ∧
      0≤ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D ∧
      ρ/4≤ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D ∧
      ρ*rsv+2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+u=ρ ∧
      u*D=2*∑w,(1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
        ordinaryAssignedShortWeight F hF K i₀ rsv θ c w) ∧
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
      (∀w j,0≤q w j) ∧ (∀w,∑j,q w j≤1/8) ∧
      (∀w j,0≤s w j) ∧ (∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)) ∧
      (∀w,q w false=0 ∧ s w false=rsv) := by
  obtain ⟨p,p₂,u,hp,hp₂,hu,hsum,hpEq,hplo,hpd,hud,hq,hQ,hs,hS,hfalse⟩:=
    ordinary_assigned_class_sampling_witness hn F hF Allowed hAllowed K hK i₀ rsv θ c ρ D d hd
      hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize hsclass hclass
  have hNamed : p₂=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D := by
    unfold ordinaryAssignedApproxRimProbability
    exact (eq_div_iff (ne_of_gt hD)).2 hpd
  refine ⟨u,hu,by simpa [← hNamed] using hp₂,by simpa [← hNamed] using hplo,?_,hud,hq,hQ,hs,hS,hfalse⟩
  rw [← hNamed]
  linarith
end Oberwolfach
