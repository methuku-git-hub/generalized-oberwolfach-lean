module

public import Oberwolfach.Vortex

@[expose] public section
/-! The first inner domain of the pre-exposure vortex has the original
    host-density margin and the exact assigned parent balance up to its
    vortex error, uniformly at every ambient vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem ordinary_first_vortex_parent_density_balance
    {V U:Type} [Fintype V] [Fintype U]
    (P:SimpleGraph V) (D m:ℕ) (β ε θ α ρ pH:ℝ)
    (Q:Vortex U P D β ε m) (hn:0<Fintype.card V)
    (hρ:ρ=initialIndexDensity U D) (hρpos:0<ρ) (hpH:0≤pH)
    (hdegree:(θ+α)*Fintype.card V≤D):
    (∀v,(θ+α-β/2)*(Q.vertices 1).card≤
      (((Q.vertices 1)∩P.neighborFinset v).card:ℝ)) ∧
    (∀v,|(ρ*pH)*((Q.vertices 1)∩P.neighborFinset v).card-
      2*pH*(Q.indices 1).card|≤(ρ*pH)*β*(Q.vertices 1).card) := by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD:(θ+α)≤(D:ℝ)/Fintype.card V:=(le_div_iff₀ hnR).2 (by simpa [mul_comm] using hdegree)
  have hA:(0:ℝ)≤(Q.vertices 1).card:=by positivity
  have hρp:0≤ρ*pH:=mul_nonneg hρpos.le hpH
  constructor
  · intro v
    have hv:v∈Q.vertices (1-2):=by simp [Q.initial]
    have hdeg:=Q.degrees 1 (by have := Q.length_pos; omega) (by omega) v hv
    have hcoeff:=mul_le_mul_of_nonneg_right hD hA
    rw [Finset.inter_comm] at hdeg
    have hh:=(abs_le.mp hdeg).1
    nlinarith only [hcoeff,hh]
  · intro v
    have hv:v∈Q.vertices (1-2):=by simp [Q.initial]
    have hcent: |((P.neighborFinset v∩Q.vertices 1).card:ℝ)-
        2*((Q.indices 1).card:ℝ)/ρ|≤β*(Q.vertices 1).card:=by
      rw [hρ]
      exact (Q.centre_estimates 1 (by have := Q.length_pos; omega) (by omega)).2 v hv
    rw [Finset.inter_comm] at hcent
    have heq:(ρ*pH)*((Q.vertices 1∩P.neighborFinset v).card:ℝ)-2*pH*(Q.indices 1).card =
      (ρ*pH)*(((Q.vertices 1∩P.neighborFinset v).card:ℝ)-2*((Q.indices 1).card:ℝ)/ρ):=by
      field_simp [hρpos.ne']
      <;> ring
    rw [heq,abs_mul,abs_of_nonneg hρp]
    nlinarith only [mul_le_mul_of_nonneg_left hcent hρp]
end Oberwolfach
