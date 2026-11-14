module

public import Oberwolfach.FirstVortexResidualTargetBudget
public import Oberwolfach.InnerRequiredTargets
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.first_inner_vertex_size_upper
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0≤ε):
    ((Q.extendedVertices 1).card:ℝ)≤ε*(Fintype.card V:ℝ):=by
  have hh:=(Q.extended_successor_size_bounds he 0).1
  have hzero:Q.extendedVertices 0=Finset.univ:=by
    rw [Q.extendedVertices_eq (by omega),Q.initial]
  simpa only [Nat.zero_add,hzero,Finset.card_univ] using hh

theorem first_vortex_residual_target_size_from_local_rows
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (inner:Finset U) (A:Finset (Fin n)) (reserved selected absorber occupied:U→Finset (Fin n))
    (d:ℕ) (hd:0<d) (θ ρ₀ ε η ζ lam a γ:ℝ)
    (hθ:0<θ) (hρ₀:ρ₀≤1) (hε:ε≤(ρ₀/4)/80000)
    (hI:(A.card:ℝ)≤ε*n) (hsub:(A.card:ℝ)^(3/4:ℝ)≤η*n)
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hlam:0≤lam) (hlam1:lam≤1) (hinv:1/(d:ℝ)≤θ/1024)
    (ha:a≤lam/(10*(d:ℝ))) (hγ:γ≤lam/(10*(d:ℝ)))
    (hrow:∀w∈inner,((innerRequiredTargets inner A reserved selected absorber occupied w).card:ℝ)≤
      2*θ*A.card+(A.card:ℝ)^(3/4:ℝ)+ζ*A.card+max a γ*n):
    ∀w,((innerRequiredTargets inner A reserved selected absorber occupied w).card:ℝ)≤(θ/1024)*n:=by
  have hcoef:=first_vortex_residual_target_coefficient d hd θ ρ₀ ε η ζ lam a γ hθ hρ₀ hε hη hζ hlam hlam1 hinv ha hγ
  have hA:(A.card:ℝ)≤n:=by exact_mod_cast (le_trans (Finset.card_le_univ A) (by simp))
  intro w
  by_cases hw:w∈inner
  · have hr:=hrow w hw
    have h1:=mul_le_mul_of_nonneg_left hI (by positivity : 0≤2*θ)
    have h2:=mul_le_mul_of_nonneg_left hA hζ0
    have hn:(0:ℝ)≤n:=by positivity
    have h3:=mul_le_mul_of_nonneg_right hcoef hn
    nlinarith
  · have hz:innerRequiredTargets inner A reserved selected absorber occupied w=∅:=by
      simp [innerRequiredTargets,hw]
    rw [hz]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
end Oberwolfach
