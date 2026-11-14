module

public import Oberwolfach.LongBinaryPartitionParameters
public import Oberwolfach.SelectedClassDensityDichotomy

@[expose] public section
/-! For a retained class, the original vortex density and sampling recipe
supply both exact binary half-degrees and the one-class/complement split. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_binary_pruned_parameters
    {I U:Type} [Fintype I] [DecidableEq I] [Fintype U] (ρclass:I→ℝ) (r ρ₀ s:ℝ)
    (i:I) (D:ℕ) (a b:U→ℝ) (hD:0<D) (heven:Even D)
    (hnonneg:∀j,0≤ρclass j) (htotal:∑j,ρclass j=1) (hlow:∀j,r≤ρclass j)
    (hclass:ρclass i/2*D=Fintype.card U) (hρlo:ρ₀≤ initialIndexDensity U D):
    let ρ:=initialIndexDensity U D
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑w,b w)/(D:ℝ)
    let k₂:=(∑w,a w)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-s-a w-b w))/(D:ℝ)
    let m:=binaryClassMultiplicity D (Fintype.card U);
    (∑j,m j)=D/2 ∧
      (∀j,expandedBinaryProbability p k p₂ k₂ u j/2*D=(m j:ℝ)) ∧
      (ρ=1 ∨ ∀j,r≤expandedBinaryProbability p k p₂ k₂ u j):=by
  intro ρ p k p₂ k₂ u m
  have hDreal:(D:ℝ)≠0:=by exact_mod_cast (ne_of_gt hD)
  have heq:ρ=ρclass i:=by
    dsimp [ρ,initialIndexDensity]
    rw [←hclass]
    field_simp
  have hρhi:ρ≤1:=by
    rw [heq]
    have hh:=Finset.single_le_sum (fun j _=>hnonneg j) (Finset.mem_univ i)
    linarith [htotal]
  have hsize:ρ*D=2*Fintype.card U:=by
    dsimp [ρ,initialIndexDensity]
    field_simp
  obtain ⟨hs,hm,h0,h1⟩:=long_binary_partition_parameters ρ₀ ρ s D a b hD heven hρlo hρhi hsize
  refine ⟨hs,hm,?_⟩
  rcases selected_class_index_density_dichotomy ρclass r i D hD hnonneg htotal hlow hclass with hone|hboth
  · exact Or.inl hone
  · right
    intro j
    fin_cases j
    · change r≤expandedBinaryProbability p k p₂ k₂ u 0
      rw [h0]
      simpa [ρ] using hboth 0
    · change r≤expandedBinaryProbability p k p₂ k₂ u 1
      rw [h1]
      simpa [ρ] using hboth 1
end Oberwolfach
