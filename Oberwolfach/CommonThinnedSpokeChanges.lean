module

public import Oberwolfach.ThinnedMarkedSeedEvent
public import Oberwolfach.TypedMarkedPotentialDegreeStability

@[expose] public section

/-! Deterministic transfer for fixed common-witness selectors. The same
coin array and parent weights are used before and after retention. A
changed common-class membership must change a spoke in one of the two
fixed columns; no sampling density multiplies this realized loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

def commonThinnedSpokes (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (b : Bool) (x : V) (_ : Unit) : Prop :=
  H b x u ∧ H b x u' ∧ (b=false → κ x=true)

theorem commonThinnedSpokes_change_columns (H H' : Bool→V→U→Prop) (κ : V→Bool)
    (u u' : U) (δ : ℝ)
    (hc : ∀ b w,(∑ x,if ¬(H b x w↔H' b x w) then (1:ℝ) else 0)≤δ) (b : Bool) :
    (∑ x,bipAdj (fun x z=>¬(commonThinnedSpokes H κ u u' b x z↔
      commonThinnedSpokes H' κ u u' b x z)) x ())≤2*δ := by
  have hpoint (x : V) :
      bipAdj (fun x z=>¬(commonThinnedSpokes H κ u u' b x z↔commonThinnedSpokes H' κ u u' b x z)) x ()≤
      (if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)+(if ¬(H b x u'↔H' b x u') then 1 else 0) := by
    by_cases h₁ : H b x u↔H' b x u
    · by_cases h₂ : H b x u'↔H' b x u'
      · have hh : commonThinnedSpokes H κ u u' b x ()↔commonThinnedSpokes H' κ u u' b x () :=
          and_congr h₁ (and_congr h₂ Iff.rfl)
        simp only [bipAdj,hh,not_true_eq_false,ite_false,h₁,h₂,add_zero,le_refl]
      · simp only [bipAdj,h₁,h₂,not_true_eq_false,not_false_eq_true,ite_false,ite_true,zero_add]
        split_ifs <;> norm_num
    · by_cases h₂ : H b x u'↔H' b x u'
      · simp only [bipAdj,h₁,h₂,not_true_eq_false,not_false_eq_true,ite_false,ite_true,add_zero]
        split_ifs <;> norm_num
      · simp only [bipAdj,h₁,h₂,not_false_eq_true,ite_true]
        split_ifs <;> norm_num
  calc
    _ ≤ ∑ x,((if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)+(if ¬(H b x u'↔H' b x u') then 1 else 0)) :=
      Finset.sum_le_sum (fun x _=>hpoint x)
    _ ≤ δ+δ := by rw [Finset.sum_add_distrib];exact add_le_add (hc b u) (hc b u')
    _ = _ := by ring

theorem commonThinnedSpokes_potential_load_change
    {tail head : E→V} {ktail khead : K→V} {m b : ℕ} {π : Equiv.Perm V}
    {H₀ Hₖ : V→Unit→Prop}
    (hm : 3≤m) (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ→ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R : E⊕K→Prop) (H H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (δ : ℝ) (hδ : 0≤δ)
    (hc : ∀ j z,(∑ x,if ¬(H j x z↔H' j x z) then (1:ℝ) else 0)≤δ)
    (j : Bool) (v : V) :
    |typedMarkedPotentialLoad w R (commonThinnedSpokes H' κ u u') (Sum.inr (j,v,()))-
      typedMarkedPotentialLoad w R (commonThinnedSpokes H κ u u') (Sum.inr (j,v,()))|≤
      10*((m:ℝ)+1)^4*B*δ/Fintype.card V := by
  have hcol := commonThinnedSpokes_change_columns H H' κ u u' δ hc
  have hrow (j : Bool) (v : V) :
      (∑ z : Unit,bipAdj (fun x z=>¬(commonThinnedSpokes H κ u u' j x z↔
        commonThinnedSpokes H' κ u u' j x z)) v z)≤2*δ := by
    simp only [Fintype.sum_unique]
    apply le_trans _ (hcol j)
    exact Finset.single_le_sum
      (f:=fun x : V=>bipAdj (fun x z=>¬(commonThinnedSpokes H κ u u' j x z↔
        commonThinnedSpokes H' κ u u' j x z)) x ())
      (fun x _=>by unfold bipAdj;split_ifs <;> norm_num) (Finset.mem_univ v)
  have hh := typedMarkedPotentialLoad_spoke_degree_stability hm hn w B hB hw R R
    (commonThinnedSpokes H κ u u') (commonThinnedSpokes H' κ u u') (2*δ) (by positivity)
    (by intro x;simp;positivity) (by intro x;simp;positivity) hrow
    (by intro j z;cases z;exact hcol j) j v ()
  exact hh.trans_eq (by ring)

end Oberwolfach
