module

public import Oberwolfach.MarkedRetainedPotentialLoadRelabel
public import Oberwolfach.VortexInitialDomainInverse

@[expose] public section
/-! The fixed parent potential-load bound transfers to level zero of the
vortex with the same sample, weights, marginals and error. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]
variable (G : SimpleGraph V) (D n₀ : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε n₀)
local instance initialLoadVertexDecEq : DecidableEq V := fun a b => Classical.propDecidable (a = b)
local instance initialLoadLocalVertexDecEq : DecidableEq (Q.vertices 0) := fun a b => Classical.propDecidable (a = b)
local instance initialLoadLocalHubDecEq : DecidableEq (Q.indices 0) := fun a b => Classical.propDecidable (a = b)
local instance initialLoadLocalNonempty : Nonempty (Q.vertices 0) :=
  ⟨vortexInitialVertexOrderIso G D n₀ β ε Q (Classical.choice inferInstance)⟩

theorem marked_vortex_initial_parent_load_bound
    (π : Equiv.Perm V) (d m : ℕ) (a c : Γ) (j : Color)
    (p k : ℝ) (q : U → Γ → ℝ) (s : U → Color → ℝ) (error : ℝ)
    (z : RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (w : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ _ => True) (fun _ _ => True) → ℝ) :
    let F := vortexInitialVertexOrderEmbedding G D n₀ β ε Q
    let f := vortexInitialVertexEquiv G D n₀ β ε Q
    let g := (vortexInitialHubEquiv G D n₀ β ε Q).symm
    let ρ := vortexInitialPermutation G D n₀ β ε Q π
    let hc : ∀ x, f (ρ x) = π (f x) := vortex_initial_vertex_equiv_commutes G D n₀ β ε Q π
    let z' := markedRetainedPairRestriction f g π ρ hc d a z
    let e := f.prodCongr f
    let M := markedWheelVertexEmbedding (m:=m) (b:=3*d) f.toEmbedding g.toEmbedding hc e e
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      (fun _ _ h=>h) (fun _ _ h=>h)
    let H := retainedRawMarkedSpokes π d (fun e => z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e => z.1 (Sum.inr e)) a)) z.2 c j
    let H' := retainedRawMarkedSpokes ρ d (fun e => z'.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet ρ d (fun e => z'.1 (Sum.inr e)) a)) z'.2 c j
    (∀ root,rawMarkedWheelMarginal G π d p k q s c j root≠0 →
      |typedMarkedPotentialLoad w (rawMarkedPairRims G π d z.1) H root-1|≤error) →
    ∀ root,rawMarkedWheelMarginal (G.comap F) ρ d p k (fun u=>q (g u)) (fun u=>s (g u)) c j root≠0 →
      |typedMarkedPotentialLoad (fun W=>w (M W)) (rawMarkedPairRims (G.comap F) ρ d z'.1) H' root-1|≤error := by
  classical
  dsimp only
  exact marked_retained_parent_load_bound_relabel (vortexInitialVertexOrderEmbedding G D n₀ β ε Q)
    (vortexInitialVertexEquiv G D n₀ β ε Q) (vortex_initial_embedding_equiv_agree G D n₀ β ε Q)
    (vortexInitialHubEquiv G D n₀ β ε Q).symm π (vortexInitialPermutation G D n₀ β ε Q π)
    (vortex_initial_vertex_equiv_commutes G D n₀ β ε Q π) G d m a c j p k q s error z w
end Oberwolfach
