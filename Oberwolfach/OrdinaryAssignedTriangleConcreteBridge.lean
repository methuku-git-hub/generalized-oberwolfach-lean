module

public import Oberwolfach.OrdinaryCombinedTriangleEvent
public import Oberwolfach.OrdinaryAssignedClassRecipeValid

@[expose] public section
/-! Substitute the actual class probabilities into a generic common-event
estimate without altering the sample or the event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) triangleFiniteEquality0 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq (Fin n)

theorem ordinary_actual_triangle_class_event_from_uniform_estimate
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U] [DecidableEq U]
    (Factors:U→SimpleGraph (Fin n)) (hFactors:∀w,(Factors w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θfreq caux ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100) (hcaux:8≤caux)
    (hda:1/θfreq≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (Factors w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (Factors w) K=some i₀)
    (k:ℕ) (P Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (θhost α pstar βP ηP ηH βH c B:ℝ) (weight:OrdinaryCycle P 3→ℝ)
    (hpstar:0<pstar) (hRlo:pstar≤ρ*rsv) (hRhi:ρ*rsv≤1)
    (hgeneric:∀ (q:U→Bool→ℝ) (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
      (hSc:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)),
      (∀w,s w false=rsv)→
      let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>ρ*rsv)
        (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hSc);
      1-(1/(n:ℝ)+3/(n:ℝ)^2)≤μ.probability
        (ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false)):
    let q:=ordinaryAssignedMarkedProbability Factors hFactors K θfreq caux
    let s:=ordinaryAssignedSpokeProbability Factors hFactors K i₀ rsv θfreq caux;
    ∃ (hq:∀w j,0≤q w j) (hQ:∀w,∑j,q w j≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑j,q w j)),
      let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>ρ*rsv)
        (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hSc);
      1-(1/(n:ℝ)+3/(n:ℝ)^2)≤μ.probability
        (ordinaryCombinedTriangleEvent d k P Conflict π θhost α pstar βP ηP ηH βH c B (ρ*rsv) rsv weight false) := by
  obtain ⟨hq,hQ,hs,hSc,hj⟩:=ordinary_assigned_class_recipe_valid hn Factors hFactors K hK i₀ rsv θfreq caux ρ D d hd
    hs0 hs1 hθfreq hθfreq1 hcaux hda hρ hρ1 hD hsize S hS hsclass hclass
  exact ⟨hq,hQ,hs,hSc,hgeneric _ hq hQ _ hs hSc hj⟩
end Oberwolfach
