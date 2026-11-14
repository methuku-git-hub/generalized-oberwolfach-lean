module

public import Oberwolfach.CommonEvents
public import Oberwolfach.ConvexDistanceProjection

@[expose] public section

/-! Invariance of the convex-distance exponential-moment assertion under
a bijective relabelling of the independent coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_convexDistance_reindex
    {I J Ω : Type*} [Fintype I] [Fintype J] [Fintype Ω]
    (e : I ≃ J) (μ : J → FiniteLaw Ω)
    (ih : ∀ B : Finset (I → Ω),
      0<(FiniteLaw.pi (fun i=>μ (e i))).probability (fun x=>x∈B) →
      (FiniteLaw.pi (fun i=>μ (e i))).expectation
        (fun x=>Real.exp (convexDistanceSq B x/4))≤
      ((FiniteLaw.pi (fun i=>μ (e i))).probability (fun x=>x∈B))⁻¹)
    (A : Finset (J → Ω))
    (hA : 0<(FiniteLaw.pi μ).probability (fun x=>x∈A)) :
    (FiniteLaw.pi μ).expectation (fun x=>Real.exp (convexDistanceSq A x/4))≤
      ((FiniteLaw.pi μ).probability (fun x=>x∈A))⁻¹ := by
  classical
  let P := Equiv.piCongrLeft (fun _ : J=>Ω) e
  let R : (J → Ω) → (I → Ω) := fun x i=>x (e i)
  have hRP (x : I → Ω) : R (P x)=x := by
    funext i
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  have hPR (x : J → Ω) : P (R x)=x := by
    funext j
    obtain ⟨i,rfl⟩ := e.surjective j
    exact Equiv.piCongrLeft_apply_apply _ _ _ _
  let B := A.image R
  have hmem (x : I → Ω) : x∈B ↔ P x∈A := by
    constructor
    · intro hx
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
      rw [← he,hPR]
      exact hy
    · intro hx
      exact Finset.mem_image.mpr ⟨P x,hx,hRP x⟩
  have hp : (FiniteLaw.pi μ).probability (fun x=>x∈A)=
      (FiniteLaw.pi (fun i=>μ (e i))).probability (fun x=>x∈B) := by
    rw [finiteLaw_pi_reindex_probability e μ]
    congr 1
    funext x
    exact propext (hmem x).symm
  have hd (x : I → Ω) : convexDistanceSq B x=convexDistanceSq A (P x) := by
    have hh := convexDistanceSq_reindex e A (P x)
    change convexDistanceSq B (R (P x))=convexDistanceSq A (P x) at hh
    rwa [hRP] at hh
  have he : (FiniteLaw.pi μ).expectation (fun x=>Real.exp (convexDistanceSq A x/4))=
      (FiniteLaw.pi (fun i=>μ (e i))).expectation
        (fun x=>Real.exp (convexDistanceSq B x/4)) := by
    rw [finiteLaw_pi_reindex_expectation e μ]
    congr 1
    funext x
    rw [hd]
  rw [he,hp]
  exact ih B (hp ▸ hA)

end Oberwolfach
