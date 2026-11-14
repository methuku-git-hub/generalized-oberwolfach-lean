module

public import Oberwolfach.SparseCorrectionMatrices
public import Oberwolfach.BipartiteCutChanges
public import Oberwolfach.TypedMatrixRealization

@[expose] public section

/-! Normalized large cuts after deleting the induced protected rectangle.
The cut cutoff is unchanged; the coefficient loss uses the actual relative
sizes of the forbidden row and column sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem bipartite_normalized_cut_scale (hn:0<Fintype.card X) (hm:0<Fintype.card Y)
    (S:Finset X) (T:Finset Y) (h:ℝ):
    h*Fintype.card X*Fintype.card Y*min ((S.card:ℝ)/Fintype.card X) ((T.card:ℝ)/Fintype.card Y)=
      h*min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card):=by
  have hx:(Fintype.card X:ℝ)≠0:=by exact_mod_cast Nat.ne_of_gt hn
  have hy:(Fintype.card Y:ℝ)≠0:=by exact_mod_cast Nat.ne_of_gt hm
  have hz:(0:ℝ)≤(Fintype.card X:ℝ)*Fintype.card Y:=by positivity
  have he:(Fintype.card X:ℝ)*Fintype.card Y*
      min ((S.card:ℝ)/Fintype.card X) ((T.card:ℝ)/Fintype.card Y)=
      min ((Fintype.card Y:ℝ)*S.card) ((Fintype.card X:ℝ)*T.card):=by
    rw [mul_min_of_nonneg _ _ hz]
    congr 1 <;> field_simp <;> ring
  calc
    _ = h*((Fintype.card X:ℝ)*Fintype.card Y*
        min ((S.card:ℝ)/Fintype.card X) ((T.card:ℝ)/Fintype.card Y)):=by ring
    _ = _:=by rw [he]

theorem bipartiteLargeCut_after_relation_changes
    (hn:0<Fintype.card X) (hm:0<Fintype.card Y) (P Q:X→Y→Prop) (δ h ζ:ℝ) (hζ:0≤ζ)
    (hrow:∀ x,(∑ y,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card Y)
    (hcol:∀ y,(∑ x,if ¬(P x y↔Q x y) then (1:ℝ) else 0)≤ζ*Fintype.card X)
    (hcut:BipartiteLargeCut (relationMultiplicity P) δ h):
    BipartiteLargeCut (relationMultiplicity Q) δ (h-ζ):=by
  intro S T hST
  have hh:=hcut S T hST
  have hcutEq (R:X→Y→Prop):
      ((∑ x,∑ y,if x∈S∧y∈T then relationMultiplicity R x y else 0:ℕ):ℝ)=
        (bipartiteMatrixCut (relationMultiplicity R) S T:ℝ):=by
    congr 1
    simp only [bipartiteMatrixCut]
    have he (x:X) (y:Y): (if x∈S∧y∈T then relationMultiplicity R x y else 0)=
        if x∈S then (if y∈T then relationMultiplicity R x y else 0) else 0:=by
      by_cases hx:x∈S <;> by_cases hy:y∈T <;> simp [hx,hy]
    simp only [he,Finset.sum_ite_irrel,Finset.sum_const_zero,←Finset.sum_filter,
      Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [hcutEq P,bipartite_normalized_cut_scale hn hm S T h] at hh
  rw [hcutEq Q,bipartite_normalized_cut_scale hn hm S T (h-ζ)]
  exact bipartite_cut_lower_after_changes P Q ζ hζ hrow hcol h S T hh

theorem bipartiteLargeCut_delete_rectangle
    (hn:0<Fintype.card X) (hm:0<Fintype.card Y) (P:X→Y→Prop) (A:Finset X) (B:Finset Y)
    (δ h ζ:ℝ) (hζ:0≤ζ) (hA:(A.card:ℝ)≤ζ*Fintype.card X) (hB:(B.card:ℝ)≤ζ*Fintype.card Y)
    (hcut:BipartiteLargeCut (relationMultiplicity P) δ h):
    BipartiteLargeCut (relationMultiplicity (fun x y=>P x y∧¬(x∈A∧y∈B))) δ (h-ζ):=by
  apply bipartiteLargeCut_after_relation_changes hn hm P _ δ h ζ hζ _ _ hcut
  · intro x
    calc
      _ ≤∑ y,if y∈B then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum
        intro y _
        by_cases hp:P x y <;> by_cases hx:x∈A <;> by_cases hy:y∈B <;> simp [hp,hx,hy]
      _ = (B.card:ℝ):=by simp
      _ ≤ _:=hB
  · intro y
    calc
      _ ≤∑ x,if x∈A then (1:ℝ) else 0:=by
        apply Finset.sum_le_sum
        intro x _
        by_cases hp:P x y <;> by_cases hx:x∈A <;> by_cases hy:y∈B <;> simp [hp,hx,hy]
      _ = (A.card:ℝ):=by simp
      _ ≤ _:=hA

end Oberwolfach
