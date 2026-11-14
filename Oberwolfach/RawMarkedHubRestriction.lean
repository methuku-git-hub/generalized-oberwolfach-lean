module

public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! A fixed injective restriction of hubs preserves the exact raw product
law. Both physical coordinates and the interval coordinates at each retained
hub keep their original distributions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Z Γ Color : Type} [Fintype V] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U] [DecidableEq Z]

def rawMarkedHubCoordinate (f : Z→U) : RawWheelCoordinate V Z→RawWheelCoordinate V U
  | Sum.inl e=>Sum.inl e
  | Sum.inr (z,i)=>Sum.inr (f z,i)

def rawMarkedHubState (f : Z→U) : ∀ e : RawWheelCoordinate V Z,
    RawMarkedCoordinateState Γ Color (rawMarkedHubCoordinate f e)→RawMarkedCoordinateState Γ Color e
  | Sum.inl _,a=>a
  | Sum.inr _,a=>a

def rawMarkedRestrictHubs (f : Z→U) (σ : RawMarkedOutcome V U Γ Color) : RawMarkedOutcome V Z Γ Color :=
  fun e=>rawMarkedHubState f e (σ (rawMarkedHubCoordinate f e))

theorem rawMarkedHubCoordinate_injective (f : Z→U) (hf : Function.Injective f) :
    Function.Injective (rawMarkedHubCoordinate (V:=V) f) := by
  intro e e' he
  cases e with
  | inl e=>cases e' <;> simp_all [rawMarkedHubCoordinate]
  | inr a=>
    cases e' with
    | inl e'=>simp_all [rawMarkedHubCoordinate]
    | inr a'=>
      simp only [rawMarkedHubCoordinate,Sum.inr.injEq,Prod.mk.injEq] at he
      exact congrArg Sum.inr (Prod.ext (hf he.1) he.2)

theorem rawMarked_hub_restriction_probability
    (f : Z→U) (hf : Function.Injective f)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (E : RawMarkedOutcome V Z Γ Color→Prop) :
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>E (rawMarkedRestrictHubs f σ))=
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd
      (fun z=>q (f z)) (fun z=>hq (f z)) (fun z=>hQ (f z))
      (fun z=>s (f z)) (fun z=>hs (f z)) (fun z=>hS (f z)))).probability E := by
  let μ := rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS
  have hh := finiteLaw_pi_injective_projection_event μ (rawMarkedHubCoordinate f)
    (rawMarkedHubCoordinate_injective f hf) (fun σ=>E (fun e=>rawMarkedHubState f e (σ e)))
  change (FiniteLaw.pi μ).probability (fun σ=>E (fun e=>rawMarkedHubState f e (σ (rawMarkedHubCoordinate f e))))=_
  rw [hh,← finiteLaw_map_probability,finiteLaw_pi_map]
  have he (e : RawWheelCoordinate V Z) :
      ((μ (rawMarkedHubCoordinate f e)).map (rawMarkedHubState (Γ:=Γ) (Color:=Color) f e))=
      rawMarkedWheelLaw p k hp hk hsum d hd
        (fun z=>q (f z)) (fun z=>hq (f z)) (fun z=>hQ (f z))
        (fun z=>s (f z)) (fun z=>hs (f z)) (fun z=>hS (f z)) e := by
    apply finiteLaw_ext
    intro a
    cases e with
    | inl e=>simp [μ,rawMarkedWheelLaw,rawMarkedHubCoordinate,rawMarkedHubState,FiniteLaw.map]
    | inr e=>simp [μ,rawMarkedWheelLaw,rawMarkedHubCoordinate,rawMarkedHubState,FiniteLaw.map,rawIntervalFamilyLaw]
  simp_rw [he]

theorem rawMarkedRestrictHubs_rims (f : Z→U) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) :
    rawMarkedPairRims P π d (rawMarkedRestrictHubs f σ)=rawMarkedPairRims P π d σ := by rfl

theorem rawMarkedRestrictHubs_spokes (f : Z→U) (π : Equiv.Perm V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (g : Γ) (j : Color) (a : Bool) (v : V) (z : Z) :
    rawMarkedPairSpokes π d (rawMarkedRestrictHubs f σ) g j a v z ↔
      rawMarkedPairSpokes π d σ g j a v (f z) := by cases a <;> rfl

end Oberwolfach
