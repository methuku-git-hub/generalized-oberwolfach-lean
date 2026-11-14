module

public import Oberwolfach.ExponentialMarkedReferenceCuts

@[expose] public section
/-! The spoke large-cut condition at a larger fixed target implies the
condition at any smaller nonnegative target. Rim conditions and profiles
are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_cut_density_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color) (α p k t₀ t:ℝ)
    (ht:0≤t₀) (hbound:t₀≤t) (σ:RawMarkedOutcome V U Γ Color)
    (hc:MarkedReferenceCutFamilies P π d g j α p k t σ):
    MarkedReferenceCutFamilies P π d g j α p k t₀ σ:=by
  constructor
  · intro b X Y hXY
    have hXY':1-t/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U:=by linarith
    have hm:0≤min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card):=by positivity
    have hh:=mul_le_mul_of_nonneg_right (show t₀/8≤t/8 by linarith) hm
    exact hh.trans (hc.1 b X Y hXY')
  · exact hc.2
end Oberwolfach
