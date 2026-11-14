module

public import Oberwolfach.PhysicalOrdinaryTupleWeight

@[expose] public section
/-! Parameter-budgeted positional estimates for the fixed ordered weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ}

section
variable (hn:1≤n) (hnV:0<Fintype.card V) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)

include hn hnV hw hB hb he

theorem physicalOrdinaryTupleWeight_edge_positions (τ:ℝ)
    (hbudget:5*((n+2:ℕ):ℝ)^4*B*(2*b)/Fintype.card V≤τ)
    (i:Fin (n+2)) (x y:V) (hxy:P.Adj x y) (hclose:¬PermutationClose π b x y):
    (1-τ≤∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0) ∧
    ((∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0)≤1+τ):=by
  have hh:=separated_physical_position_edge_error (P:=P) (π:=π) (b:=b) hn hnV w hw B hB hb he i x y hxy hclose
  have heq:(∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0)=
      (∑ C:SeparatedTuple π b (n+2),if C.val i=x ∧ C.val (cycleNext i)=y then
        separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0):=by
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> simp [physicalOrdinaryTupleWeight_of_separated]
  rw [heq]
  have herror:=abs_le.mp (hh.trans hbudget)
  constructor <;> linarith [herror.1,herror.2]

theorem physicalOrdinaryTupleWeight_vertex_positions (D τ ε:ℝ)
    (hdeg:∀ x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudget:6*((n+2:ℕ):ℝ)^4*B*(2*b)+ε*(Fintype.card V:ℝ)≤τ*D)
    (i:Fin (n+2)) (x:V):
    ((1-τ)*D≤∑ C:SeparatedTuple π b (n+2),if C.val i=x then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0) ∧
    ((∑ C:SeparatedTuple π b (n+2),if C.val i=x then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0)≤(1+τ)*D):=by
  have hh:=separated_physical_position_vertex_error (P:=P) (π:=π) (b:=b) hn hnV w hw B hB hb he i x
  have heq:(∑ C:SeparatedTuple π b (n+2),if C.val i=x then
      physicalOrdinaryTupleWeight (π:=π) (b:=b) hn w C.val else 0)=
      (∑ C:SeparatedTuple π b (n+2),if C.val i=x then
        separatedOrderedWeight hn (fun H=>w (separatedHostCycleToOrdinary H)) C else 0):=by
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> simp [physicalOrdinaryTupleWeight_of_separated]
  rw [heq]
  have hh':=abs_le.mp hh
  have hd':=abs_le.mp (hdeg x)
  constructor <;> nlinarith [hh'.1,hh'.2,hd'.1,hd'.2,hbudget]
end
end Oberwolfach
