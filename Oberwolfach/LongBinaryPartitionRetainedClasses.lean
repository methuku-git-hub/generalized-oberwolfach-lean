module

public import Oberwolfach.BinaryComplementClassDensity

@[expose] public section
/-! The original class partition supplies the density alternatives required
by the binary protected-class construction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_binary_partition_from_retained_classes
    {U I:Type} [Fintype U] [Fintype I] (density:I→ℝ) (i:I) (r s:ℝ) (D:ℕ) (a b:U→ℝ)
    (hD:0<D) (heven:Even D) (hρ:∀j,0≤density j) (hsum:∑j,density j=1)
    (hsmall:∀j,density j=0 ∨ r≤density j) (hcurrent:r≤density i)
    (hsize:density i*D=2*Fintype.card U):
    let ρ:=density i
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑w,b w)/(D:ℝ)
    let k₂:=(∑w,a w)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-s-a w-b w))/(D:ℝ)
    let m:=binaryClassMultiplicity D (Fintype.card U);
    (∑j,m j)=D/2 ∧ (∀j,expandedBinaryProbability p k p₂ k₂ u j/2*D=(m j:ℝ)) ∧
    (2*p+2*k+2*p₂+2*k₂+u=1 ∨ ∀j,r≤expandedBinaryProbability p k p₂ k₂ u j) := by
  dsimp only
  have hle:density i≤1:=by
    have h:=Finset.single_le_sum (fun j _=>hρ j) (Finset.mem_univ i)
    simpa only [hsum] using h
  obtain ⟨hm,hmass,h0,h1⟩:=long_binary_partition_parameters r (density i) s D a b hD heven hcurrent hle hsize
  refine ⟨hm,hmass,?_⟩
  rcases binary_complement_density_from_nonempty_classes density r hρ hsum hsmall i with hone|hcomp
  · left
    have hd:0<(D:ℝ):=by exact_mod_cast hD
    have hx:=(long_expanded_class_density_and_floor r (density i) D s a b hd hcurrent hsize).2
    rw [expanded_physical_class_mass] at hx
    simpa only [hone] using hx
  · right
    intro j
    by_cases hj:j=0
    · rw [hj,h0]; exact hcurrent
    · have hj1:j=1:=by omega
      rw [hj1,h1]; exact hcomp
end Oberwolfach
