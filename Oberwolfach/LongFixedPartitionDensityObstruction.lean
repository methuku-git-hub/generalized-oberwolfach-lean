module

public import Oberwolfach.FirstVortexInitialMatchingVortexRates

@[expose] public section
/-! A fixed lower bound on every nonzero part is unavailable when the
complement of the distinguished density can be positive and arbitrarily small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_fixed_partition_density_obstruction
    {I:Type} [Fintype I] (density:I→ℝ) (i:I) (ρ rPart:ℝ)
    (hρ:density i=ρ) (hnonneg:∀j,0≤density j) (hsum:∑j,density j=1)
    (hparts:∀j,density j=0 ∨ rPart≤density j)
    (hsmall:0<1-ρ) (hupper:1-ρ<rPart):False := by
  let S:Finset I:=Finset.univ.erase i
  have hrest:(∑j∈S,density j)=1-ρ:=by
    have h:=Finset.sum_erase_add (s:=Finset.univ) (f:=density) (Finset.mem_univ i)
    dsimp [S]
    linarith
  have hzero:∀j∈S,density j=0:=by
    intro j hj
    have hle:density j≤∑k∈S,density k:=by
      exact Finset.single_le_sum (fun k _=>hnonneg k) hj
    rcases hparts j with hj0|hjlarge
    · exact hj0
    · linarith
  have hz:(∑j∈S,density j)=0:=Finset.sum_eq_zero hzero
  linarith
end Oberwolfach
