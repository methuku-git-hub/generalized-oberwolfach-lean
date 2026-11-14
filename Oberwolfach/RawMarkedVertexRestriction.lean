module

public import Oberwolfach.RawMarkedHubRestriction

@[expose] public section

/-! Restricting to a fixed rim vertex domain preserves the raw coordinate law.
This assertion concerns the law alone; compatibility of the interval states
also requires invariance under the successor permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W U Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder W] [DecidableEq U]

def rawIntervalVertexCoordinate (f : W→V) : RawIntervalCoordinate W→RawIntervalCoordinate V :=
  Sum.map f (Sum.map f f)

def rawMarkedVertexCoordinate (f : W→V) : RawWheelCoordinate W U→RawWheelCoordinate V U
  | Sum.inl e=>Sum.inl (Sym2.map f e)
  | Sum.inr (u,i)=>Sum.inr (u,rawIntervalVertexCoordinate f i)

def rawMarkedVertexState (f : W→V) : ∀ e : RawWheelCoordinate W U,
    RawMarkedCoordinateState Γ Color (rawMarkedVertexCoordinate f e)→RawMarkedCoordinateState Γ Color e
  | Sum.inl _,a=>a
  | Sum.inr (_,Sum.inl _),a=>a
  | Sum.inr (_,Sum.inr (Sum.inl _)),a=>a
  | Sum.inr (_,Sum.inr (Sum.inr _)),a=>a

def rawMarkedRestrictVertices (f : W→V) (σ : RawMarkedOutcome V U Γ Color) : RawMarkedOutcome W U Γ Color :=
  fun e=>rawMarkedVertexState f e (σ (rawMarkedVertexCoordinate f e))

theorem rawMarkedVertexCoordinate_injective (f : W→V) (hf : Function.Injective f) :
    Function.Injective (rawMarkedVertexCoordinate (U:=U) f) := by
  have hi : Function.Injective (rawIntervalVertexCoordinate f) := Sum.map_injective.mpr ⟨hf,Sum.map_injective.mpr ⟨hf,hf⟩⟩
  intro e e' he
  cases e with
  | inl e=>
    cases e' with
    | inl e'=>exact congrArg Sum.inl (Sym2.map.injective hf (Sum.inl.inj he))
    | inr e'=>cases he
  | inr a=>
    cases e' with
    | inl e'=>cases he
    | inr a'=>
      simp only [rawMarkedVertexCoordinate,Sum.inr.injEq,Prod.mk.injEq] at he
      exact congrArg Sum.inr (Prod.ext he.1 (hi he.2))

theorem rawMarked_vertex_restriction_probability
    (f : W→V) (hf : Function.Injective f)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (E : RawMarkedOutcome W U Γ Color→Prop) :
    (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>E (rawMarkedRestrictVertices f σ))=
    (FiniteLaw.pi (rawMarkedWheelLaw (V:=W) p k hp hk hsum d hd q hq hQ s hs hS)).probability E := by
  let μ := rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS
  have hh := finiteLaw_pi_injective_projection_event μ (rawMarkedVertexCoordinate f)
    (rawMarkedVertexCoordinate_injective f hf) (fun σ=>E (fun e=>rawMarkedVertexState f e (σ e)))
  change (FiniteLaw.pi μ).probability (fun σ=>E (fun e=>rawMarkedVertexState f e (σ (rawMarkedVertexCoordinate f e))))=_
  rw [hh,← finiteLaw_map_probability,finiteLaw_pi_map]
  have he (e : RawWheelCoordinate W U) :
      ((μ (rawMarkedVertexCoordinate f e)).map (rawMarkedVertexState (Γ:=Γ) (Color:=Color) f e))=
      rawMarkedWheelLaw (V:=W) p k hp hk hsum d hd q hq hQ s hs hS e := by
    apply finiteLaw_ext
    intro a
    cases e with
    | inl e=>simp [μ,rawMarkedWheelLaw,rawMarkedVertexCoordinate,rawMarkedVertexState,FiniteLaw.map]
    | inr e=>
      rcases e with ⟨u,i⟩
      cases i with
      | inl i=>simp [μ,rawMarkedWheelLaw,rawMarkedVertexCoordinate,rawMarkedVertexState,FiniteLaw.map,rawIntervalFamilyLaw,rawIntervalVertexCoordinate,rawIntervalCoordinateLaw]
      | inr i=>cases i <;> simp [μ,rawMarkedWheelLaw,rawMarkedVertexCoordinate,rawMarkedVertexState,FiniteLaw.map,rawIntervalFamilyLaw,rawIntervalVertexCoordinate,rawIntervalCoordinateLaw]
  simp_rw [he]

end Oberwolfach
