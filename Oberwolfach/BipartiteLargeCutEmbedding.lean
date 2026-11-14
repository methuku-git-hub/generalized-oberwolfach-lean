module

public import Oberwolfach.BipartiteNormalizedCutDeletion

@[expose] public section

/-! A normalized large cut survives restriction to large embedded parts.
The cutoff change is explicit; the cut coefficient is not rescaled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y A B:Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]

theorem bipartiteLargeCut_sum_restrict (L:X→Y→ℕ) (S:Finset X) (T:Finset Y):
    (∑ x,∑ y,if x∈S∧y∈T then L x y else 0:ℕ)=bipartiteMatrixCut L S T:=by
  unfold bipartiteMatrixCut
  have he (x:X) (y:Y):(if x∈S∧y∈T then L x y else 0)=
      if x∈S then (if y∈T then L x y else 0) else 0:=by split_ifs <;> simp_all
  simp only [he,Finset.sum_ite_irrel,Finset.sum_const_zero,←Finset.sum_filter,
    Finset.filter_mem_eq_inter,Finset.univ_inter]

theorem bipartiteMatrixCut_embedding (f:A↪X) (g:B↪Y) (L:X→Y→ℕ) (S:Finset A) (T:Finset B):
    bipartiteMatrixCut L (S.image f) (T.image g)=bipartiteMatrixCut (fun x y=>L (f x) (g y)) S T:=by
  unfold bipartiteMatrixCut
  rw [Finset.sum_image (fun _ _ _ _ he=>f.injective he)]
  apply Finset.sum_congr rfl
  intro x hx
  exact Finset.sum_image (fun _ _ _ _ he=>g.injective he)

theorem bipartiteLargeCut_embedding (f:A↪X) (g:B↪Y) (L:X→Y→ℕ)
    (hA:0<Fintype.card A) (hB:0<Fintype.card B)
    (κ δ δA h:ℝ) (hκ:0<κ) (hh:0≤h)
    (hAsize:κ*Fintype.card X≤(Fintype.card A:ℝ))
    (hBsize:κ*Fintype.card Y≤(Fintype.card B:ℝ))
    (hcutoff:1-2*δ≤κ*(1-2*δA)) (hcut:BipartiteLargeCut L δ h):
    BipartiteLargeCut (fun x y=>L (f x) (g y)) δA h:=by
  have hAX:Fintype.card A≤Fintype.card X:=Fintype.card_le_of_injective f f.injective
  have hBY:Fintype.card B≤Fintype.card Y:=Fintype.card_le_of_injective g g.injective
  have hX:0<Fintype.card X:=lt_of_lt_of_le hA hAX
  have hY:0<Fintype.card Y:=lt_of_lt_of_le hB hBY
  have ha:(0:ℝ)<Fintype.card A:=by exact_mod_cast hA
  have hb:(0:ℝ)<Fintype.card B:=by exact_mod_cast hB
  have hx:(0:ℝ)<Fintype.card X:=by exact_mod_cast hX
  have hy:(0:ℝ)<Fintype.card Y:=by exact_mod_cast hY
  intro S T hST
  have hSratio:κ*((S.card:ℝ)/Fintype.card A)≤(S.card:ℝ)/Fintype.card X:=by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ ha hx).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hAsize (Nat.cast_nonneg (α:=ℝ) S.card)]
  have hTratio:κ*((T.card:ℝ)/Fintype.card B)≤(T.card:ℝ)/Fintype.card Y:=by
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ hb hy).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hBsize (Nat.cast_nonneg (α:=ℝ) T.card)]
  have hlarge:1-2*δ<((S.image f).card:ℝ)/Fintype.card X+((T.image g).card:ℝ)/Fintype.card Y:=by
    rw [Finset.card_image_of_injective _ f.injective,Finset.card_image_of_injective _ g.injective]
    have hscaled:=mul_lt_mul_of_pos_left hST hκ
    nlinarith only [hscaled,hcutoff,hSratio,hTratio]
  have hparent:=hcut (S.image f) (T.image g) hlarge
  rw [bipartiteLargeCut_sum_restrict,bipartiteMatrixCut_embedding,
    bipartite_normalized_cut_scale hX hY (S.image f) (T.image g) h,
    Finset.card_image_of_injective _ f.injective,Finset.card_image_of_injective _ g.injective] at hparent
  rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hA hB S T h]
  apply le_trans _ hparent
  apply mul_le_mul_of_nonneg_left _ hh
  apply min_le_min
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hBY) (Nat.cast_nonneg S.card)
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hAX) (Nat.cast_nonneg T.card)

end Oberwolfach
