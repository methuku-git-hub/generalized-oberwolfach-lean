module

public import Oberwolfach.ThreeBlockHall
public import Oberwolfach.BipartiteBlockMatching

@[expose] public section

/-! The three-block matching survives a bounded-degree forbidden relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem three_block_matching_after_deletion {X Y : Type*} [Fintype X] [Fintype Y]
    (E J : X → Y → Prop) (P : X → Prop) (Q : Y → Prop)
    (hcard : Fintype.card X=Fintype.card Y)
    (d a lam B : ℝ) (ha : 0<a) (hlam : 0<lam)
    (hdegree : 2*a+B≤d) (hmargin : B<lam*a)
    (hgap : ((Finset.univ.filter P).card:ℝ)+2*a≤(Finset.univ.filter (fun y => ¬Q y)).card)
    (B₃ : BipartiteBlockBounds E P (fun y => ¬Q y) d a lam)
    (B₄ : BipartiteBlockBounds E (fun x => ¬P x) (fun y => ¬Q y) d a lam)
    (B₅ : BipartiteBlockBounds E (fun x => ¬P x) Q d a lam)
    (hjrow : ∀ x, ((Finset.univ.filter (J x)).card:ℝ)≤B)
    (hjcol : ∀ y, ((Finset.univ.filter (fun x => J x y)).card:ℝ)≤B) :
    ∃ g : X ≃ Y, ∀ x, E x (g x) ∧ ¬J x (g x) := by
  classical
  have hrow (x : X) : d≤((Finset.univ.filter (E x)).card:ℝ) := by
    by_cases hx : P x
    · exact (B₃.row x hx).trans (Nat.cast_le.mpr (block_row_le_full E _ x))
    · exact (B₄.row x hx).trans (Nat.cast_le.mpr (block_row_le_full E _ x))
  have hcol (y : Y) : d≤((Finset.univ.filter (fun x => E x y)).card:ℝ) := by
    by_cases hy : Q y
    · exact (B₅.col y hy).trans (Nat.cast_le.mpr (block_row_le_full (fun y x => E x y) _ y))
    · exact (B₄.col y hy).trans (Nat.cast_le.mpr (block_row_le_full (fun y x => E x y) _ y))
  apply three_block_perfect_matching (fun x y => E x y ∧ ¬J x y) P Q hcard a ha
  · intro x
    have hh := degree_after_bounded_relation_deletion (E x) (J x) d B (hrow x) (hjrow x)
    have hh' : 2*a≤((Finset.univ.filter (fun y => E x y ∧ ¬J x y)).card:ℝ) := by linarith
    convert hh' using 1 <;> congr!
  · intro y
    have hh := degree_after_bounded_relation_deletion (fun x => E x y) (fun x => J x y) d B (hcol y) (hjcol y)
    have hh' : 2*a≤((Finset.univ.filter (fun x => E x y ∧ ¬J x y)).card:ℝ) := by linarith
    convert hh' using 1 <;> congr!
  · exact hgap
  · intro S T hS hT htype
    have hc : lam*S.card*T.card≤(bipartiteMatrixCut (fun x y => if E x y then 1 else 0) S T:ℝ) := by
      rcases htype with ⟨hp,hq|hq⟩ | ⟨hp,hq⟩
      · exact B₅.cut S T hp hq hS hT
      · exact B₄.cut S T hp hq hS hT
      · exact B₃.cut S T hp hq hS hT
    exact large_cut_after_bounded_deletion E J S T a B lam ha hlam hmargin hS hT hjrow hc

end Oberwolfach
