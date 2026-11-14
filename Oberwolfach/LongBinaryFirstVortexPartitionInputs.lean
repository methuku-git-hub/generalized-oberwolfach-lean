module

public import Oberwolfach.LongBinaryPartitionRetainedClasses
public import Oberwolfach.LongFirstVortexProtectionGraph

@[expose] public section
/-! Instantiate the binary protected-class inputs with the actual first
vortex set and the original retained class multiplicities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_binary_first_vortex_partition_inputs
    {n D m:ℕ} {U I:Type} [Fintype U] [Fintype I]
    (G:SimpleGraph (Fin n)) (β ε αHost:ℝ) (Q:Vortex U G D β ε m)
    (density:I→ℝ) (i:I) (r s:ℝ) (a b:U→ℝ)
    (hD:0<D) (heven:Even D) (hρ:∀j,0≤density j) (hsum:∑j,density j=1)
    (hsmall:∀j,density j=0 ∨ r≤density j) (hcurrent:r≤density i)
    (hsize:density i*D=2*Fintype.card U) (hε:0≤ε) (hεsmall:ε≤αHost/100000):
    let ρ:=density i
    let p:=ρ*(1/100)/2
    let k:=ρ*s/2
    let p₂:=(∑w,b w)/(D:ℝ)
    let k₂:=(∑w,a w)/(D:ℝ)
    let u:=2*(∑w,(1-1/100-s-a w-b w))/(D:ℝ)
    let mult:=binaryClassMultiplicity D (Fintype.card U)
    let Inner:=Q.extendedVertices 1
    let Protect:=spanningRestriction (⊤:SimpleGraph (Fin n)) Inner;
    (∑j,mult j)=D/2 ∧ (∀j,expandedBinaryProbability p k p₂ k₂ u j/2*D=(mult j:ℝ)) ∧
    (2*p+2*k+2*p₂+2*k₂+u=1 ∨ ∀j,r≤expandedBinaryProbability p k p₂ k₂ u j) ∧
    (∀v,(Protect.degree v:ℝ)≤αHost/100000*n) ∧
    (∀x∈Inner,∀y∈Inner,x≠y→Protect.Adj x y) ∧ mult 0=Fintype.card U :=by
  intro ρ p k p₂ k₂ u mult Inner Protect
  obtain ⟨hm,hmass,hlower⟩:=long_binary_partition_from_retained_classes density i r s D a b hD heven hρ hsum hsmall hcurrent hsize
  obtain ⟨hprotect,hclique⟩:=long_first_vortex_protection_graph G D m β ε αHost Q hε hεsmall
  exact ⟨hm,hmass,hlower,hprotect,hclique,by simp [mult,binaryClassMultiplicity]⟩
end Oberwolfach
