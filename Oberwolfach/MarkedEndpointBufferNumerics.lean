module

public import Oberwolfach.MarkedEndpointBlockNumerics

@[expose] public section

/-! Extra margins for the repeated endpoint assignments. The larger
blocks provide both the final degree and the subsequent deletion budget. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem bipartite_block_weaken_degree {X Y:Type} [Fintype X] [Fintype Y]
    (E:X→Y→Prop) (P:X→Prop) (Q:Y→Prop) (d d' tau lam:ℝ)
    (h:BipartiteBlockBounds E P Q d tau lam) (hd:d'≤d):
    BipartiteBlockBounds E P Q d' tau lam:=
  ⟨fun x hx=>hd.trans (h.row x hx),fun y hy=>hd.trans (h.col y hy),h.cut⟩

theorem marked_endpoint_buffer_numerics (t a eta:ℝ) (ht:0<t) (ha:0<a)
    (heta:0<eta) (hsmall:eta≤t*a/32):
    ∀ d:ℕ,∃ N:ℕ,∀ n:ℕ,N≤n→
      2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(t*a/4)*n ∧
      (2*(2*(3*d)+1):ℕ)<(t/4)*(eta*n) ∧
      ∀ loss:ℝ,loss≤(t*a/4)*n→(t*a/4)*n+loss≤(t*a/2)*n:=by
  intro d
  let B:ℝ:=6*d+1
  obtain ⟨N,hN⟩:=exists_nat_gt (max (16*B/(t*a)) (8*B/(t*eta)))
  refine ⟨N,?_⟩
  intro n hn
  have hn':(N:ℝ)≤n:=Nat.cast_le.mpr hn
  have h1:16*B<(n:ℝ)*(t*a):=
    (div_lt_iff₀ (mul_pos ht ha)).mp (((le_max_left _ _).trans_lt hN).trans_le hn')
  have h2:8*B<(n:ℝ)*(t*eta):=
    (div_lt_iff₀ (mul_pos ht heta)).mp (((le_max_right _ _).trans_lt hN).trans_le hn')
  have hetan:=mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)
  have hp:0≤t*a*n:=mul_nonneg (mul_pos ht ha).le (Nat.cast_nonneg n)
  refine ⟨?_,?_,?_⟩
  · dsimp [B] at h1
    push_cast
    nlinarith only [h1,hetan,hp]
  · dsimp [B] at h2
    push_cast
    nlinarith only [h2]
  · intro loss hloss
    linarith only [hloss]

end Oberwolfach
