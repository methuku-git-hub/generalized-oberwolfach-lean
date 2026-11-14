module

public import Oberwolfach.BipartiteLargeCutEmbedding
public import Oberwolfach.DirectedCutBounds

@[expose] public section
/-! Normalize a matrix cut on a fixed inner subtype without changing its
    vertex set or orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_matrix_cut_normalized
    {V:Type} [Fintype V] [DecidableEq V] (I:Finset V) (A:V→V→ℕ) (δ h:ℝ) (hI:0<I.card)
    (hcut:∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
      h*I.card*min (S.card:ℝ) T.card≤(matrixCut (fun x y:I=>A x.val y.val) S T:ℝ)):
    BipartiteLargeCut (fun x y:I=>A x.val y.val) δ h:=by
  have hn:0<Fintype.card I:=by simpa only [Fintype.card_coe] using hI
  have hn':(0:ℝ)<I.card:=by exact_mod_cast hI
  intro S T hST
  have hlarge:(1-2*δ)*I.card<(S.card:ℝ)+T.card:=by
    simp only [Fintype.card_coe,←add_div] at hST
    exact (lt_div_iff₀ hn').mp hST
  have hh:=hcut S T hlarge
  rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hn hn]
  simp only [Fintype.card_coe,←mul_min_of_nonneg _ _ (Nat.cast_nonneg I.card)]
  convert hh using 1 <;> first | rfl | ring
end Oberwolfach
