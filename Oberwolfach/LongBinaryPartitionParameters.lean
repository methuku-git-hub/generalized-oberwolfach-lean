module

public import Oberwolfach.BinaryClassMultiplicity
public import Oberwolfach.ExpandedBinaryClassLaw
public import Oberwolfach.LongExpandedClassDensityAndFloor

@[expose] public section
/-! The original long-class sampling recipe supplies the exact binary
partition densities and integral degrees. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_binary_partition_parameters
    {U:Type} [Fintype U] (ρ₀ ρ s:ℝ) (D:ℕ) (a b:U→ℝ)
    (hD:0<D) (heven:Even D) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hsize:ρ*D=2*Fintype.card U):
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑w,b w)/(D:ℝ)
    let k₂:=(∑w,a w)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-s-a w-b w))/(D:ℝ)
    let m:=binaryClassMultiplicity D (Fintype.card U);
    (∑i,m i)=D/2 ∧
      (∀i,expandedBinaryProbability p k p₂ k₂ u i/2*D=(m i:ℝ)) ∧
      expandedBinaryProbability p k p₂ k₂ u 0=ρ ∧
      expandedBinaryProbability p k p₂ k₂ u 1=1-ρ:=by
  intro p k p₂ k₂ u m
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  obtain ⟨_,hmass⟩:=long_expanded_class_density_and_floor ρ₀ ρ (D:ℝ) s a b hDreal hρlo hsize
  have hsum:2*p+2*k+2*p₂+2*k₂+u=ρ:=by
    exact (expanded_physical_class_mass p k p₂ k₂ u).symm.trans hmass
  obtain ⟨hs,hm0,hm1⟩:=binary_class_multiplicity_exact D (Fintype.card U) ρ heven hρhi hsize
  have h0:expandedBinaryProbability p k p₂ k₂ u 0=ρ:=by
    simp [expandedBinaryProbability];exact hsum
  have h1:expandedBinaryProbability p k p₂ k₂ u 1=1-ρ:=by
    simp [expandedBinaryProbability];linarith
  refine ⟨hs,?_,h0,h1⟩
  intro i
  fin_cases i
  · simpa [h0] using hm0
  · simpa [h1] using hm1
end Oberwolfach
