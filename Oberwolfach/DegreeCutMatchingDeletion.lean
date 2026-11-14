module

public import Oberwolfach.DegreeCutHall
public import Oberwolfach.BipartiteQuadraticCut

@[expose] public section

/-! A bounded-degree deletion preserves the Hall conclusion when every
large cut originally has positive density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem filter_card_le_kept_add_deleted {Z : Type*} [Fintype Z]
    (P Q : Z→Prop) :
    (Finset.univ.filter P).card≤(Finset.univ.filter (fun z=>P z∧¬Q z)).card+
      (Finset.univ.filter Q).card := by
  classical
  have hs : Finset.univ.filter P⊆(Finset.univ.filter (fun z=>P z∧¬Q z))∪(Finset.univ.filter Q):=by
    intro z hz
    by_cases hq : Q z
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2,hq⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem degree_cut_matching_after_deletion {X Y : Type*} [Fintype X] [Fintype Y]
    (E J : X→Y→Prop) (hcard : Fintype.card X=Fintype.card Y)
    (a b lam : ℝ) (ha : 0<a) (hb : 0≤b) (hlam : 0<lam) (hmargin : b<lam*a)
    (hrow : ∀ x,a+b≤((Finset.univ.filter (E x)).card:ℝ))
    (hcol : ∀ y,a+b≤((Finset.univ.filter (fun x=>E x y)).card:ℝ))
    (hjrow : ∀ x,((Finset.univ.filter (J x)).card:ℝ)≤b)
    (hjcol : ∀ y,((Finset.univ.filter (fun x=>J x y)).card:ℝ)≤b)
    (hcut : ∀ S : Finset X,∀ T : Finset Y,a≤(S.card:ℝ) → a≤(T.card:ℝ) →
      lam*S.card*T.card≤(bipartiteMatrixCut (fun x y=>if E x y then 1 else 0) S T:ℝ)) :
    ∃ σ : X≃Y,∀ x,E x (σ x)∧¬J x (σ x) := by
  classical
  apply degree_cut_perfect_matching (fun x y=>E x y∧¬J x y) hcard a ha.le
  · intro x
    have hh:=filter_card_le_kept_add_deleted (E x) (J x)
    have hhR : ((Finset.univ.filter (E x)).card:ℝ)≤
      (Finset.univ.filter (fun y=>E x y∧¬J x y)).card+(Finset.univ.filter (J x)).card:=by exact_mod_cast hh
    have hk : a≤((Finset.univ.filter (fun y=>E x y∧¬J x y)).card:ℝ):=by linarith only [hhR,hrow x,hjrow x]
    convert hk using 1 <;> congr!
  · intro y
    have hh:=filter_card_le_kept_add_deleted (fun x=>E x y) (fun x=>J x y)
    have hhR : ((Finset.univ.filter (fun x=>E x y)).card:ℝ)≤
      (Finset.univ.filter (fun x=>E x y∧¬J x y)).card+(Finset.univ.filter (fun x=>J x y)).card:=by exact_mod_cast hh
    have hk : a≤((Finset.univ.filter (fun x=>E x y∧¬J x y)).card:ℝ):=by linarith only [hhR,hcol y,hjcol y]
    convert hk using 1 <;> congr!
  · intro S T hS hT hSn hTn
    by_contra hn
    have hinc : ∀ x∈S,∀ y∈T,E x y → J x y:=by
      intro x hx y hy he
      by_contra hj
      exact hn ⟨x,hx,y,hy,he,hj⟩
    have hupper : (bipartiteMatrixCut (fun x y=>if E x y then 1 else 0) S T:ℝ)≤(S.card:ℝ)*b:=by
      simp only [bipartiteMatrixCut,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      calc
        _ ≤ ∑ _x∈S,b:=by
          apply Finset.sum_le_sum
          intro x hx
          calc
            _ ≤ ∑ y∈T,if J x y then (1:ℝ) else 0:=by
              apply Finset.sum_le_sum
              intro y hy
              by_cases he : E x y
              · simp [he,hinc x hx y hy he]
              · simp only [he,ite_false];positivity
            _ ≤ ∑ y,if J x y then (1:ℝ) else 0:=Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (by intro y hy hyt;positivity)
            _ ≤ b:=by simpa using hjrow x
        _ = _:=by simp
    have hpositive : (0:ℝ)<S.card:=Nat.cast_pos.mpr hSn.card_pos
    have hlarge : b<lam*T.card:=hmargin.trans_le (mul_le_mul_of_nonneg_left hT hlam.le)
    have hstrict:=mul_lt_mul_of_pos_left hlarge hpositive
    have hlower:=hcut S T hS hT
    nlinarith only [hstrict,hupper,hlower]

end Oberwolfach
