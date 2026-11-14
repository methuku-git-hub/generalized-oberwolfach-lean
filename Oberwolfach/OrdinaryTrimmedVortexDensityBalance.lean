module

public import Oberwolfach.VortexExtended

@[expose] public section
/-! Parent-density and sampled balance on actual differences of two vortex
    levels, using the original regular host and index-density identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_trimmed_vortex_density_balance
    {V U:Type} [Fintype V] [Fintype U]
    (P:SimpleGraph V) (D m:ℕ) (β ε θ α ρ pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:ρ=initialIndexDensity U D) (hρpos:0<ρ) (hβ:0≤β) (hε:0≤ε) (hεsmall:ε≤1/4) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D) (j k:ℕ) (hjk:j<k):
    let A:=Q.extendedVertices j\Q.extendedVertices k;
    let B:=Q.extendedIndices j\Q.extendedIndices k;
    (∀x∈Q.extendedVertices (k-2),
      (θ+α-(10/3:ℝ)*β)*A.card≤((A∩P.neighborFinset x).card:ℝ)) ∧
    (∀x∈Q.extendedVertices (k-2),
      |(ρ*pH)*(A∩P.neighborFinset x).card-2*pH*B.card|≤(ρ*pH)*(5/3:ℝ)*β*A.card):=by
  intro A B
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD:(θ+α)≤(D:ℝ)/Fintype.card V:=(le_div_iff₀ hnR).2 (by simpa [mul_comm] using hdegree)
  have hA:(0:ℝ)≤A.card:=by positivity
  have hρp:0≤ρ*pH:=mul_nonneg hρpos.le hpH
  have hρinit:(0:ℝ) < initialIndexDensity U D:=by rwa [←hρ]
  constructor
  · intro x hx
    have h:=Q.extended_difference_degree_estimates hreg hn hρinit hβ hε hεsmall hjk x hx
    rw [←hρ] at h
    change |2*(B.card:ℝ)/ρ-((D:ℝ)/Fintype.card V)*A.card|≤(5/3:ℝ)*β*A.card ∧
      |((P.neighborFinset x∩A).card:ℝ)-2*(B.card:ℝ)/ρ|≤(5/3:ℝ)*β*A.card at h
    have htri:=abs_sub_le ((P.neighborFinset x∩A).card:ℝ) (2*(B.card:ℝ)/ρ)
      (((D:ℝ)/Fintype.card V)*A.card)
    have hsum:|((P.neighborFinset x∩A).card:ℝ)-((D:ℝ)/Fintype.card V)*A.card|≤
      (10/3:ℝ)*β*A.card:=by nlinarith only [htri,h.1,h.2]
    rw [Finset.inter_comm] at hsum
    have hlo:=(abs_le.mp hsum).1
    have hcoeff:=mul_le_mul_of_nonneg_right hD hA
    nlinarith only [hlo,hcoeff]
  · intro x hx
    have h:=Q.extended_difference_degree_estimates hreg hn hρinit hβ hε hεsmall hjk x hx
    rw [←hρ] at h
    have hcent:|((P.neighborFinset x∩A).card:ℝ)-2*(B.card:ℝ)/ρ|≤(5/3:ℝ)*β*A.card:=by
      convert h.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [Finset.inter_comm] at hcent
    have heq:(ρ*pH)*((A∩P.neighborFinset x).card:ℝ)-2*pH*B.card=
      (ρ*pH)*(((A∩P.neighborFinset x).card:ℝ)-2*(B.card:ℝ)/ρ):=by
      field_simp [hρpos.ne'] <;> ring
    rw [heq,abs_mul,abs_of_nonneg hρp]
    nlinarith only [mul_le_mul_of_nonneg_left hcent hρp]
end Oberwolfach
