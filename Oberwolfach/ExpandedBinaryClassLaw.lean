module

public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! Grouping states zero through four into the sampled class retains their
original fair direction bit and yields the exact two-colour law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def expandedBinaryClass (z:Fin 6×Bool):Fin 2×Bool:=
  (if z.1=5 then 1 else 0,z.2)

def expandedBinaryProbability (p k p₂ k₂ u:ℝ):Fin 2→ℝ:=
  ![2*p+2*k+2*p₂+2*k₂+u,1-2*p-2*k-2*p₂-2*k₂-u]

theorem expanded_binary_probability_nonneg
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (a:Fin 2):
    0≤expandedBinaryProbability p k p₂ k₂ u a:=by
  fin_cases a <;> simp [expandedBinaryProbability] <;> linarith

theorem expanded_binary_probability_sum (p k p₂ k₂ u:ℝ):
    ∑a,expandedBinaryProbability p k p₂ k₂ u a=1:=by
  simp [Fin.sum_univ_succ,expandedBinaryProbability]

theorem expanded_binary_class_law
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1):
    (FiniteLaw.categoricalDirection (markedExpandedPhysicalProbability p k p₂ k₂ u)
      (markedExpandedPhysicalProbability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (markedExpandedPhysicalProbability_sum p k p₂ k₂ u)).map expandedBinaryClass=
    FiniteLaw.categoricalDirection (expandedBinaryProbability p k p₂ k₂ u)
      (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
      (expanded_binary_probability_sum p k p₂ k₂ u):=by
  apply finiteLaw_ext
  intro z
  rcases z with ⟨a,b⟩
  fin_cases a <;> cases b <;>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedExpandedPhysicalProbability,
      expandedBinaryProbability,expandedBinaryClass,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool] <;> ring
end Oberwolfach
