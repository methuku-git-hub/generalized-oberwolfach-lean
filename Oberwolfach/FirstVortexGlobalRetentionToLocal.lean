module

public import Oberwolfach.RetentionLocalFromGlobal
public import Oberwolfach.FirstVortexMatchingScalePositive

@[expose] public section
/-! Select the global retention tolerance relative to the already fixed
first-vortex scale, uniformly for every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_global_retention_to_local
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hε1:ε≤1) (hm:0<m)
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (ζglobal ζlocal:ℝ) (hζlocal:0≤ζlocal) (hζ:ζglobal≤ζlocal*ε/2)
    (hglobal:RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J):
    RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J :=by
  have hsize:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hscale:ζglobal*Fintype.card V≤ζlocal*(Q.extendedVertices 1).card:=by
    have h₁:=mul_le_mul_of_nonneg_right hζ (Nat.cast_nonneg (Fintype.card V))
    have h₂:=mul_le_mul_of_nonneg_left hsize hζlocal
    nlinarith only [h₁,h₂]
  have hrow:ζglobal≤ζlocal:=by nlinarith [mul_nonneg hζlocal (sub_nonneg.mpr hε1)]
  exact retained_restriction_local_from_global π d σ g t (Q.extendedVertices 1) ζglobal ζlocal J hglobal hscale hrow
end Oberwolfach
