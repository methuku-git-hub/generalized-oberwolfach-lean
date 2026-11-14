module

public import Oberwolfach.OrdinaryTerminalCandidates

@[expose] public section
/-! A terminal pair of total order at most t has at most 2^(t^2)
admissible balanced remainders, uniformly in the ambient host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_terminal_candidate_uniform_count (r m t:ℕ) (Q:SimpleGraph V)
    (H:V→U→Prop) (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤t):
    Fintype.card (OrdinaryTerminalCandidate r m Q H W B)≤2^(t*t):=by
  have hw:W.card≤t:=by omega
  have hh:W.card*(W.card+B.card)≤t*t:=Nat.mul_le_mul hw hsize
  have he:W.card*W.card+W.card*B.card≤t*t:=by simpa [Nat.mul_add] using hh
  exact (ordinary_terminal_candidate_card_bound r m Q H W B).trans
    (Nat.pow_le_pow_right (by norm_num) he)
end Oberwolfach
