module

public import Oberwolfach.VortexLocalRowSizeConditions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem Vortex.first_inner_vertex_size_lower
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m) (he:0<ε)
    (hpos:1≤(Q.extendedVertices 1).card):
    ε*(Fintype.card V:ℝ)/2≤(Q.extendedVertices 1).card:=by
  have hl:1≤Q.length:=Q.length_pos
  have h:=Q.extended_previous_card_le he (i:=1) le_rfl hl hpos
  have hzero:Q.extendedVertices 0=Finset.univ:=by
    rw [Q.extendedVertices_eq (by omega),Q.initial]
  have h':(Fintype.card V:ℝ)≤(2/ε)*(Q.extendedVertices 1).card:=by
    simpa only [Nat.sub_self,hzero,Finset.card_univ] using h
  have hh:=mul_le_mul_of_nonneg_left h' he.le
  have he0:ε≠0:=ne_of_gt he
  field_simp at hh
  nlinarith only [hh]
end Oberwolfach
