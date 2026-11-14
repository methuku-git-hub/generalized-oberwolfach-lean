module

public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! Size and density hypotheses for the physical preparation law follow from
the regular host and its actual index set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_initial_sizes {V U:Type*} [Fintype V] [Fintype U]
    (G:SimpleGraph V) (D:ℕ) (hreg:G.IsRegularOfDegree D)
    (hn:0<Fintype.card V) (α:ℝ) (hα:0≤α)
    (hdegree:(1/2+α)*Fintype.card V≤(D:ℝ))
    (hρ:0 < initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1):
    0<D ∧ 0<Fintype.card U ∧ Fintype.card U≤Fintype.card V ∧
    (Fintype.card V:ℝ)/2≤D ∧ (D:ℝ)≤2*Fintype.card V ∧
    initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hDreal:(0:ℝ)<D:=by nlinarith
  have hD:0<D:=by exact_mod_cast hDreal
  have hID:initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by
    unfold initialIndexDensity
    field_simp
  have hUreal:(0:ℝ)<Fintype.card U:=by nlinarith [mul_pos hρ hDreal]
  have hU:0<Fintype.card U:=by exact_mod_cast hUreal
  have hρD:initialIndexDensity U D*(D:ℝ)≤(D:ℝ):=by
    nlinarith [mul_le_mul_of_nonneg_right hρ1 hDreal.le]
  have hDupper:D≤Fintype.card V:=regular_degree_le_card hreg hn
  have hUD:(2:ℝ)*Fintype.card U≤D:=by linarith
  have hUV:Fintype.card U≤Fintype.card V:=by
    have hDR:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hDupper
    have hVR:(Fintype.card U:ℝ)≤Fintype.card V:=by linarith
    exact_mod_cast hVR
  refine ⟨hD,hU,hUV,?_,?_,hID⟩
  · nlinarith
  · have hDR:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hDupper
    linarith
end Oberwolfach
