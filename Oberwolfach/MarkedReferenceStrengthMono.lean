module

public import Oberwolfach.ExponentialMarkedReferenceCuts
public import Oberwolfach.MarkedReferenceStatistics

@[expose] public section
/-! A stronger density parameter yields the same reference statistics and
cut family at any smaller parameter, on the same sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_statistics_strength_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (D ε δ γ γ' p k s t:ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (hγ:γ'≤γ) (h:MarkedReferenceStatistics P π d g j D ε δ γ p k s t σ):
    MarkedReferenceStatistics P π d g j D ε δ γ' p k s t σ:=by
  refine ⟨⟨h.1.1,?_⟩,h.2⟩
  intro x y hxy
  have hm:0≤(3/2:ℝ)*p^2*Fintype.card V:=by positivity
  have hh:=mul_le_mul_of_nonneg_right hγ hm
  have hz:=h.1.2 x y hxy
  nlinarith

theorem marked_reference_cut_strength_mono
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (α α' p k t:ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (hα:α'≤α) (hp:0≤p) (hk:0≤k)
    (h:MarkedReferenceCutFamilies P π d g j α p k t σ):
    MarkedReferenceCutFamilies P π d g j α' p k t σ:=by
  refine ⟨h.1,?_⟩
  intro b δ hδα hδp S T hST
  have hd:0≤(if b then k else p):=by split <;> assumption
  have hδα':δ≤α/32:=by linarith
  have hmul:α'*(if b then k else p)/4≤α*(if b then k else p)/4:=by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hα hd) (by norm_num)
  have hc:0≤(Fintype.card V:ℝ)*min (S.card:ℝ) T.card:=by positivity
  have ht:=mul_le_mul_of_nonneg_right hmul hc
  have hb:=h.2 b δ hδα' hδp S T hST
  nlinarith
end Oberwolfach
