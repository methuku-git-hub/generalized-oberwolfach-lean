module

public import Oberwolfach.RawIntervalSelectedLabels
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! Exact hub restriction for the original interval-colour experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] [DecidableEq Z]

def rawIntervalRestrictHubs (f : Z→U) (σ : RawIntervalFamilyOutcome V U Γ Color) : RawIntervalFamilyOutcome V Z Γ Color :=
  fun e=>σ (f e.1,e.2)

theorem rawInterval_hub_restriction_probability (f : Z→U) (hf : Function.Injective f)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (E : RawIntervalFamilyOutcome V Z Γ Color→Prop) :
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>E (rawIntervalRestrictHubs f σ))=
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd
      (fun z=>q (f z)) (fun z=>hq (f z)) (fun z=>hQ (f z))
      (fun z=>s (f z)) (fun z=>hs (f z)) (fun z=>hS (f z)))).probability E := by
  have hinj : Function.Injective (fun e : Z×RawIntervalCoordinate V=>(f e.1,e.2)) := by
    intro x y h
    exact Prod.ext (hf (Prod.mk.inj h).1) (Prod.mk.inj h).2
  exact finiteLaw_pi_injective_projection_event
    (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS) (fun e : Z×RawIntervalCoordinate V=>(f e.1,e.2)) hinj E

theorem rawIntervalRestrictHubs_state (f : Z→U) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (x : V) (z : Z) :
    rawIntervalFamilyState π d (rawIntervalRestrictHubs f σ) (x,z)=rawIntervalFamilyState π d σ (x,f z) := rfl

end Oberwolfach
