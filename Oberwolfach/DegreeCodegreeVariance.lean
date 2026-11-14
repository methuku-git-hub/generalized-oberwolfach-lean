module

public import Oberwolfach.BipartiteIntersectionEstimates
public import Oberwolfach.BipartiteQuadraticCut

@[expose] public section

/-! A cut estimate from actual degrees and upper codegrees with a bounded
set of exceptional partners at each row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem degree_codegree_variance (H:X→Y→Prop) (p ε D:ℝ)
    (hp:0≤p) (hp1:p≤1) (hε:0≤ε)
    (E:X→Finset X) (hE:∀ x,((E x).card:ℝ)≤D)
    (hrow:∀ x,(p-ε)*Fintype.card Y≤∑ u,bipAdj H x u)
    (hcodeg:∀ x y,y∉E x → ∑ u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y)
    (S:Finset X) :
    (∑ u,((∑ x∈S,bipAdj H x u)-p*S.card)^2)≤
      3*ε*S.card^2*Fintype.card Y+D*S.card*Fintype.card Y := by
  let b:ℝ:=Fintype.card Y
  let s:ℝ:=S.card
  let g:Y→ℝ:=fun u=>∑ x∈S,bipAdj H x u
  let c:X→X→ℝ:=fun x y=>∑ u,bipAdj H x u*bipAdj H y u
  have hc (x:X):∑ y∈S,c x y≤s*(p^2+ε)*b+D*b:=by
    have hpt (y:X):c x y≤(p^2+ε)*b+(if y∈E x then b else 0):=by
      by_cases hy:y∈E x
      · rw [if_pos hy]
        have hupper:c x y≤b:=by
          calc
            _ ≤ ∑ _u:Y,(1:ℝ):=Finset.sum_le_sum (fun u _=>by
              have h1:=bipAdj_le_one H x u;have h2:=bipAdj_le_one H y u
              exact (mul_le_mul h1 h2 (bipAdj_nonneg H y u) (by norm_num)).trans_eq (by ring))
            _ = _:=by simp [b]
        have hn:0≤(p^2+ε)*b:=by dsimp [b];positivity
        linarith only [hupper,hn]
      · rw [if_neg hy,add_zero];exact hcodeg x y hy
    have he:∑ y∈S,(if y∈E x then b else 0)≤D*b:=by
      calc
        _ ≤ ∑ y:X,if y∈E x then b else 0:=Finset.sum_le_univ_sum_of_nonneg (fun _=>by split_ifs <;> positivity)
        _ = (E x).card*b:=by simp
        _ ≤ _:=mul_le_mul_of_nonneg_right (hE x) (by dsimp [b];positivity)
    have hh:=Finset.sum_le_sum (fun y (_:y∈S)=>hpt y)
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hh
    dsimp [s]
    nlinarith only [hh,he]
  have hsecond:(∑ u,(g u)^2)≤s^2*(p^2+ε)*b+D*s*b:=by
    have he:(∑ u,(g u)^2)=∑ x∈S,∑ y∈S,c x y:=by
      simp only [g,pow_two,Finset.sum_mul,Finset.mul_sum,c]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [he]
    have hh:=Finset.sum_le_sum (fun x (_:x∈S)=>hc x)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    dsimp [s] at *
    nlinarith only [hh]
  have hfirst:s*(p-ε)*b≤∑ u,g u:=by
    have hh:=Finset.sum_le_sum (fun x (_:x∈S)=>hrow x)
    simp only [Finset.sum_const,nsmul_eq_mul] at hh
    rw [Finset.sum_comm] at hh
    dsimp [s,b,g]
    nlinarith only [hh]
  have he:(∑ u,((∑ x∈S,bipAdj H x u)-p*S.card)^2)=
      (∑ u,(g u)^2)-2*p*s*(∑ u,g u)+p^2*s^2*b:=by
    have hsingle (u:Y):((∑ x∈S,bipAdj H x u)-p*S.card)^2=(g u)^2-2*p*s*g u+p^2*s^2:=by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,g,s]
      ring
    simp_rw [hsingle]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    dsimp [b];ring
  rw [he]
  have hfirst':=mul_le_mul_of_nonneg_left hfirst (show 0≤2*p*s by dsimp [s];positivity)
  have herr:2*p*ε*s^2*b≤2*ε*s^2*b:=by
    have hh:=mul_le_mul_of_nonneg_right hp1 (show 0≤2*ε*s^2*b by dsimp [s,b];positivity)
    nlinarith only [hh]
  change (∑ u,(g u)^2)-2*p*s*(∑ u,g u)+p^2*s^2*b≤3*ε*s^2*b+D*s*b
  nlinarith only [hsecond,hfirst',herr]

theorem degree_codegree_cut_square (H:X→Y→Prop) (p ε D:ℝ)
    (hp:0≤p) (hp1:p≤1) (hε:0≤ε)
    (E:X→Finset X) (hE:∀ x,((E x).card:ℝ)≤D)
    (hrow:∀ x,(p-ε)*Fintype.card Y≤∑ u,bipAdj H x u)
    (hcodeg:∀ x y,y∉E x → ∑ u,bipAdj H x u*bipAdj H y u≤(p^2+ε)*Fintype.card Y)
    (S:Finset X) (T:Finset Y) :
    ((bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:ℝ)-p*S.card*T.card)^2≤
      T.card*(3*ε*S.card^2*Fintype.card Y+D*S.card*Fintype.card Y) := by
  let f:Y→ℝ:=fun u=>(∑ x∈S,bipAdj H x u)-p*S.card
  have hc:=Finset.sum_mul_sq_le_sq_mul_sq T (fun _=>(1:ℝ)) f
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  have hv:=degree_codegree_variance H p ε D hp hp1 hε E hE hrow hcodeg S
  have he:(∑ u∈T,f u)=(bipartiteMatrixCut (fun x u=>if H x u then 1 else 0) S T:ℝ)-p*S.card*T.card:=by
    simp only [f,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]
    rw [Finset.sum_comm]
    simp only [bipAdj,bipartiteMatrixCut,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    ring
  rw [he] at hc
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg T.card)
  exact (Finset.sum_le_univ_sum_of_nonneg (fun u=>sq_nonneg (f u))).trans hv

end Oberwolfach
