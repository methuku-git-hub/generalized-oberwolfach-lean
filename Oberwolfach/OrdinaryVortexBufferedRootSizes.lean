module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! Deeper vortex roots at an arbitrary fixed buffer depth shrink by the
    corresponding power of the original vortex ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U]

theorem finite_forward_geometric_bound (a:ℕ→ℝ) (ε:ℝ) (hε:0≤ε)
    (hstep:∀i,a (i+1)≤ε*a i) (i buffer:ℕ):
    a (i+buffer)≤ε^buffer*a i :=by
  induction buffer with
  | zero => simp
  | succ b ih =>
    have hh:=hstep (i+b)
    have hm:=mul_le_mul_of_nonneg_left ih hε
    rw [show i+(b+1)=i+b+1 by omega,pow_succ]
    nlinarith only [hh,hm]

theorem ordinary_vortex_buffered_root_sizes
    (P:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (hε:0≤ε) (i buffer:ℕ)
    (hU:(Q.extendedIndices i).card≤(Q.extendedVertices i).card):
    ((Q.extendedVertices (i+buffer)).card:ℝ)+(Q.extendedIndices (i+buffer)).card≤
      2*ε^buffer*(Q.extendedVertices i).card :=by
  let a:ℕ→ℝ:=fun j=>(Q.extendedVertices j).card
  let b:ℕ→ℝ:=fun j=>(Q.extendedIndices j).card
  have ha:∀j,a (j+1)≤ε*a j:=by
    intro j
    exact (Q.extended_successor_size_bounds hε j).1
  have hb:∀j,b (j+1)≤ε*b j:=by
    intro j
    exact (Q.extended_successor_size_bounds hε j).2
  have hA:=finite_forward_geometric_bound a ε hε ha i buffer
  have hB:=finite_forward_geometric_bound b ε hε hb i buffer
  have hU':b i≤a i:=by dsimp [a,b];exact_mod_cast hU
  have hpow:0≤ε^buffer:=pow_nonneg hε _
  have hUscale:=mul_le_mul_of_nonneg_left hU' hpow
  dsimp [a,b] at hA hB hUscale
  nlinarith only [hA,hB,hUscale]
end Oberwolfach
