module

public import Oberwolfach.ClassRefinementProduct
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! The five states inside a marked class are obtained by conditioning the
original physical probabilities on membership in that class. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPhysicalInsideProbability (p k p₂ k₂ u ρ:ℝ):Fin 5→ℝ:=
  ![2*p/ρ,2*k/ρ,2*p₂/ρ,2*k₂/ρ,u/ρ]

theorem marked_physical_inside_nonneg (p k p₂ k₂ u ρ:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hρ:0<ρ):
    ∀ i,0≤markedPhysicalInsideProbability p k p₂ k₂ u ρ i:=by
  intro i
  fin_cases i <;> simp [markedPhysicalInsideProbability] <;> positivity

theorem marked_physical_inside_sum (p k p₂ k₂ u ρ:ℝ) (hρ:0<ρ)
    (hbalance:2*p+2*k+2*p₂+2*k₂+u=ρ):
    ∑ i,markedPhysicalInsideProbability p k p₂ k₂ u ρ i=1:=by
  simp [Fin.sum_univ_succ,markedPhysicalInsideProbability]
  field_simp
  linarith

def markedPhysicalOptionIndex (x:Option (Fin 5)):Fin 6:=
  match x with
  | none=>5
  | some i=>⟨i.val,by omega⟩

theorem marked_physical_option_refinement (p k p₂ k₂ u ρ:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hρ:0<ρ) (hρ1:ρ≤1) (hbalance:2*p+2*k+2*p₂+2*k₂+u=ρ):
    let inside:=FiniteLaw.categorical (markedPhysicalInsideProbability p k p₂ k₂ u ρ)
      (marked_physical_inside_nonneg p k p₂ k₂ u ρ hp hk hp₂ hk₂ hu hρ)
      (marked_physical_inside_sum p k p₂ k₂ u ρ hρ hbalance);
    (FiniteLaw.optional ρ hρ.le hρ1 inside).map markedPhysicalOptionIndex=
    FiniteLaw.categorical (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu (by linarith))
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u):=by
  intro inside
  apply finiteLaw_ext
  intro i
  fin_cases i <;> simp [FiniteLaw.map,FiniteLaw.optional,FiniteLaw.categorical,
    inside,markedPhysicalInsideProbability,markedExpandedPhysicalProbability,
    markedPhysicalOptionIndex,Fintype.sum_option,Fin.sum_univ_succ] <;>
    field_simp <;> linarith
end Oberwolfach
