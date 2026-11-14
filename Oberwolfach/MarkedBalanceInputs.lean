module

public import Oberwolfach.MarkedCycleIncidence
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

/-! Converting a balanced typed-edge vector and its sup-norm bound to the
actual ordinary and marked endpoint sums used by position splitting. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem markedBalanceSubspace_inputs {V E K : Type*}
    [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (w : E⊕K → ℝ)
    (hw : w∈markedBalanceSubspace tail head ktail khead m) :
    (∀ v,occurrenceSumLinear tail (fun e => w (Sum.inl e)) v+
      occurrenceSumLinear ktail (fun e => w (Sum.inr e)) v=
      occurrenceSumLinear head (fun e => w (Sum.inl e)) v+
      occurrenceSumLinear khead (fun e => w (Sum.inr e)) v) ∧
    (∑ e : E,w (Sum.inl e))=(m:ℝ)*(∑ e : K,w (Sum.inr e)) := by
  constructor
  · intro v
    have hh := congrFun hw.1 v
    change (∑ e : E⊕K,if Sum.elim tail ktail e=v then w e else 0)=
      (∑ e : E⊕K,if Sum.elim head khead e=v then w e else 0) at hh
    change (∑ e : E,if tail e=v then w (Sum.inl e) else 0)+(∑ e : K,if ktail e=v then w (Sum.inr e) else 0)=
      (∑ e : E,if head e=v then w (Sum.inl e) else 0)+(∑ e : K,if khead e=v then w (Sum.inr e) else 0)
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] at hh
    convert hh using 1 <;> congr 1 <;> apply Finset.sum_congr rfl <;>
      intro e _ <;> split_ifs <;> rfl
  · exact hw.2

theorem edge_weight_error_of_norm {E : Type*} [Fintype E]
    (w : E → ℝ) (κ : ℝ) (hw : ‖w-(fun _ => (1:ℝ))‖≤κ) (e : E) : |w e-1|≤κ := by
  have hh := (norm_le_pi_norm (w-(fun _ => (1:ℝ))) e).trans hw
  simpa only [Pi.sub_apply,Real.norm_eq_abs] using hh

theorem graph_large_cut_monotone {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (δ δ' h h' : ℝ) (hδ : δ'≤δ) (hh : h'≤h)
    (hcut : ∀ S T : Finset V,(1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
      h*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) :
    ∀ S T : Finset V,(1-2*δ')*Fintype.card V<(S.card:ℝ)+T.card →
      h'*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ) := by
  intro S T hST
  have hnp : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have he : (1-2*δ)*Fintype.card V≤(1-2*δ')*Fintype.card V :=
    mul_le_mul_of_nonneg_right (by linarith) hnp
  have hmin : 0≤min (S.card:ℝ) T.card := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh hnp) hmin).trans
    (hcut S T (he.trans_lt hST))

theorem marked_graph_cut_uniform {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E → V) (α p p₀ : ℝ) (hα : 0≤α) (hp : p₀≤p)
    (hcut : ∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) :
    ∀ S T : Finset V,(1-2*min (α/16) (p₀/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p₀/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ) := by
  apply graph_large_cut_monotone tail head _ _ _ _ _ _ hcut
  · exact min_le_min le_rfl (div_le_div_of_nonneg_right hp (by norm_num))
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hα) (by norm_num)

end Oberwolfach
