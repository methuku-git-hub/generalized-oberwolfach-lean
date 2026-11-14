module

public import Oberwolfach.MarkedPhysicalLaw

@[expose] public section
/-! The selected and approximate directed physical states share one
categorical exposure. Forgetting the latter preserves the selected law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedExpandedPhysicalProbability (p k p₂ k₂ u:ℝ):Fin 6→ℝ :=
  ![2*p,2*k,2*p₂,2*k₂,u,1-2*p-2*k-2*p₂-2*k₂-u]

theorem markedExpandedPhysicalProbability_nonneg
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (a:Fin 6):
    0≤markedExpandedPhysicalProbability p k p₂ k₂ u a := by
  fin_cases a <;> simp [markedExpandedPhysicalProbability] <;> linarith

theorem markedExpandedPhysicalProbability_sum (p k p₂ k₂ u:ℝ):
    ∑ a,markedExpandedPhysicalProbability p k p₂ k₂ u a=1 := by
  simp [Fin.sum_univ_succ,markedExpandedPhysicalProbability]

def markedExpandedPhysicalCollapse (z:Fin 6×Bool):Option (Bool×Bool) :=
  if z.1=0 then some (false,z.2) else if z.1=1 then some (true,z.2) else none

theorem marked_expanded_physical_collapse_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map markedExpandedPhysicalCollapse=
      markedPhysicalLaw p k hp hk (by linarith) := by
  apply finiteLaw_ext
  intro z
  cases z with
  | none=>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
      markedExpandedPhysicalCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]
    ring
  | some z=>
    rcases z with ⟨b,c⟩
    cases b <;> cases c <;>
      simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
        markedExpandedPhysicalCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]

theorem marked_expanded_physical_product_collapse
    {I:Type} [Fintype I] [DecidableEq I]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.pi (fun _:I=>FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u))).map
        (fun σ i=>markedExpandedPhysicalCollapse (σ i)) =
      FiniteLaw.pi (fun _:I=>markedPhysicalLaw p k hp hk (by linarith)) := by
  rw [finiteLaw_pi_map]
  congr 1
  funext i
  exact marked_expanded_physical_collapse_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum
end Oberwolfach
