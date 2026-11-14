module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! Every successive extended level has at most the corresponding power
of the original scale, including the empty level after termination. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.extended_pair_power_size_bounds
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0≤ε) (i:ℕ):
    ((Q.extendedVertices i).card:ℝ)≤ε^i*Fintype.card V ∧
    ((Q.extendedIndices i).card:ℝ)≤ε^i*Fintype.card U :=by
  induction i with
  | zero =>
    have hV:Q.extendedVertices 0=Finset.univ:=by rw [Q.extendedVertices_eq (by omega),Q.initial]
    have hU:Q.extendedIndices 0=Finset.univ:=by rw [Q.extendedIndices_eq (by omega),Q.indices_initial]
    simp only [hV,hU,Finset.card_univ,pow_zero,one_mul,le_refl,and_self]
  | succ i ih =>
    obtain ⟨hV,hU⟩:=Q.extended_successor_size_bounds he i
    constructor
    · calc
        ((Q.extendedVertices (i+1)).card:ℝ)≤ε*(Q.extendedVertices i).card:=hV
        _≤ε*(ε^i*Fintype.card V):=mul_le_mul_of_nonneg_left ih.1 he
        _=ε^(i+1)*Fintype.card V:=by rw [pow_succ];ring
    · calc
        ((Q.extendedIndices (i+1)).card:ℝ)≤ε*(Q.extendedIndices i).card:=hU
        _≤ε*(ε^i*Fintype.card U):=mul_le_mul_of_nonneg_left ih.2 he
        _=ε^(i+1)*Fintype.card U:=by rw [pow_succ];ring
end Oberwolfach
