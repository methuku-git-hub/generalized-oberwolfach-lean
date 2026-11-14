module

public import Oberwolfach.RawMarkedRestrictionGeometry

@[expose] public section

/-! Simultaneous fixed restrictions of the vertex and hub domains keep
exactly the original law. State agreement uses the stated permutation
invariance; the law identity alone does not require it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

def rawMarkedRestrictPair (f : W→V) (g : Z→U) (σ : RawMarkedOutcome V U Γ Color) : RawMarkedOutcome W Z Γ Color :=
  rawMarkedRestrictVertices f (rawMarkedRestrictHubs g σ)

theorem rawMarked_pair_restriction_probability
    (f : W→V) (hf : Function.Injective f) (g : Z→U) (hg : Function.Injective g)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u a,0≤s u a)
    (hS : ∀ u,∑ a,s u a≤ intervalUncoveredProbability d (∑ a,q u a))
    (E : RawMarkedOutcome W Z Γ Color→Prop) :
    (FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (fun σ=>E (rawMarkedRestrictPair f g σ))=
    (FiniteLaw.pi (rawMarkedWheelLaw (V:=W) p k hp hk hsum d hd
      (fun z=>q (g z)) (fun z=>hq (g z)) (fun z=>hQ (g z))
      (fun z=>s (g z)) (fun z=>hs (g z)) (fun z=>hS (g z)))).probability E := by
  unfold rawMarkedRestrictPair
  rw [rawMarked_hub_restriction_probability g hg p k hp hk hsum d hd q hq hQ s hs hS
    (fun σ=>E (rawMarkedRestrictVertices f σ))]
  exact rawMarked_vertex_restriction_probability f hf p k hp hk hsum d hd
    (fun z=>q (g z)) (fun z=>hq (g z)) (fun z=>hQ (g z))
    (fun z=>s (g z)) (fun z=>hs (g z)) (fun z=>hS (g z)) E

theorem rawMarkedRestrictPair_rims
    (f : W↪oV) (g : Z→U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hcomm : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (e : (W×W)⊕(W×W)) :
    rawMarkedPairRims (P.comap f) ρ d (rawMarkedRestrictPair f g σ) e ↔
      rawMarkedPairRims P π d σ (Sum.map (Prod.map f f) (Prod.map f f) e) := by
  exact rawMarkedRestrictVertices_rims f π ρ hcomm P d (rawMarkedRestrictHubs g σ) e

theorem rawMarkedRestrictPair_spokes
    (f : W↪oV) (g : Z→U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hcomm : ∀ x,f (ρ x)=π (f x)) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (a : Γ) (j : Color) (b : Bool) (x : W) (z : Z) :
    rawMarkedPairSpokes ρ d (rawMarkedRestrictPair f g σ) a j b x z ↔
      rawMarkedPairSpokes π d σ a j b (f x) (g z) := by
  exact (rawMarkedRestrictVertices_spokes f π ρ hcomm d (rawMarkedRestrictHubs g σ) a j b x z).trans
    (rawMarkedRestrictHubs_spokes g π d σ a j b (f x) z)

end Oberwolfach
