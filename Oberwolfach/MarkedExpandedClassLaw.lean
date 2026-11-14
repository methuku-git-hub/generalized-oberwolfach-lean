module

public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! Projection to membership in the sampled class, retaining the shared
orientation bit even for the outside state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedExpandedClass (z:Fin 6×Bool):Fin 2×Bool :=
  (if z.1=5 then 1 else 0,z.2)

def markedClassProbability (ρ:ℝ):Fin 2→ℝ := ![ρ,1-ρ]

theorem markedClassProbability_nonneg (ρ:ℝ) (hρ:0≤ρ) (hρ1:ρ≤1) (a:Fin 2):
    0≤markedClassProbability ρ a := by fin_cases a <;> simp [markedClassProbability] <;> linarith

theorem markedClassProbability_sum (ρ:ℝ):∑ a,markedClassProbability ρ a=1 := by
  simp [Fin.sum_univ_succ,markedClassProbability]

theorem marked_expanded_class_projection
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    let ρ:=2*p+2*k+2*p₂+2*k₂+u;
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map markedExpandedClass =
    FiniteLaw.categoricalDirection (markedClassProbability ρ)
      (markedClassProbability_nonneg ρ (by linarith) hsum) (markedClassProbability_sum ρ) := by
  intro ρ
  apply finiteLaw_ext
  rintro ⟨a,b⟩
  fin_cases a <;> cases b <;>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
      markedExpandedClass,markedClassProbability,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool,ρ] <;> ring
end Oberwolfach
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_expanded_class_product_projection
    {I:Type} [Fintype I] [DecidableEq I]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    let ρ:=2*p+2*k+2*p₂+2*k₂+u;
    (FiniteLaw.pi (fun _:I=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).map
      (fun σ i=>markedExpandedClass (σ i)) =
    FiniteLaw.pi (fun _:I=>FiniteLaw.categoricalDirection (markedClassProbability ρ)
      (markedClassProbability_nonneg ρ (by linarith) hsum) (markedClassProbability_sum ρ)) := by
  intro ρ
  rw [finiteLaw_pi_map]
  congr 1
  funext i
  exact marked_expanded_class_projection p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
end Oberwolfach
