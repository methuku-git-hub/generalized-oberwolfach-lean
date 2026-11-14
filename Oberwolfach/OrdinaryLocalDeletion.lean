module

public import Oberwolfach.OrdinaryLocalLoads
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Deletion from an ordinary local-factor host. Every root remains in the
original ambient set, and the fixed parent-cycle coefficients are retained.
The loss is bounded by the degree of the actual deleted graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

theorem ordinaryLocalPotential_sdiff_loss (P Q F D : SimpleGraph V) (T : Finset V)
    (φ : OrdinaryCycle P r→ℝ) (hφ : ∀ C,0≤φ C) (v : V) :
    |ordinaryLocalPotential P (Q\D) F T φ v-ordinaryLocalPotential P Q F T φ v|≤
      ∑ C,if v∈C.val.val.support ∧
        (∃ x∈C.val.val.support,∃ y∈C.val.val.support,D.Adj x y) then φ C else 0 := by
  let a : OrdinaryCycle P r→Prop:=fun C=>v∈C.val.val.support ∧ C.val.val≤Q ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) ∧
    (∀ z∈C.val.val.support,z≠v → z∈T)
  let b : OrdinaryCycle P r→Prop:=fun C=>v∈C.val.val.support ∧ C.val.val≤Q\D ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) ∧
    (∀ z∈C.val.val.support,z≠v → z∈T)
  have hba (C) : b C→a C := fun h=>⟨h.1,h.2.1.trans sdiff_le,h.2.2⟩
  have hab (C) (ha : a C) (hb : ¬b C) :
      ∃ x∈C.val.val.support,∃ y∈C.val.val.support,D.Adj x y := by
    by_contra hn
    have hno : ∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬D.Adj x y := by
      simpa only [not_exists,not_and] using hn
    apply hb
    refine ⟨ha.1,?_,ha.2.2⟩
    intro x y hxy
    exact ⟨ha.2.1 hxy,hno x hxy.mem_support_left y hxy.mem_support_right⟩
  have hnonneg : 0≤(∑ C,if a C then φ C else 0)-(∑ C,if b C then φ C else 0) := by
    apply sub_nonneg.mpr
    apply Finset.sum_le_sum
    intro C _
    by_cases hb : b C
    · simp only [if_pos hb,if_pos (hba C hb),le_refl]
    · rw [if_neg hb];split_ifs;exact hφ C;exact le_refl _
  have haeq : ordinaryLocalPotential P Q F T φ v=∑ C,if a C then φ C else 0 := by
    unfold ordinaryLocalPotential;congr!
  have hbeq : ordinaryLocalPotential P (Q\D) F T φ v=∑ C,if b C then φ C else 0 := by
    unfold ordinaryLocalPotential;congr!
  rw [abs_sub_comm,haeq,hbeq]
  rw [abs_of_nonneg hnonneg,←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro C _
  by_cases hb : b C
  · simp only [if_pos hb,if_pos (hba C hb),sub_self]
    split_ifs;exact hφ C;exact le_refl _
  · rw [if_neg hb,sub_zero]
    by_cases ha : a C
    · rw [if_pos ha,if_pos ⟨ha.1,hab C ha hb⟩]
    · rw [if_neg ha];split_ifs;exact hφ C;exact le_refl _

theorem ordinaryLocalPotential_sdiff_bound (P Q F D : SimpleGraph V) (T : Finset V)
    (hr : 2≤r) (hn : 0<Fintype.card V) (φ : OrdinaryCycle P r→ℝ)
    (hφ : ∀ C,0≤φ C) (B L : ℝ) (hB : 0≤B)
    (hφB : ∀ C,φ C≤B/(Fintype.card V:ℝ)^(r-1))
    (hD : ∀ v,(D.degree v:ℝ)≤L) (v : V) :
    |ordinaryLocalPotential P (Q\D) F T φ v-ordinaryLocalPotential P Q F T φ v|≤
      3*(r:ℝ)^4*B*L/Fintype.card V := by
  have hnR : (0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn
  have hcoef : ∀ C,φ C≤(B/Fintype.card V)/(Fintype.card V:ℝ)^(r-2) := by
    intro C
    have he : (B/Fintype.card V)/(Fintype.card V:ℝ)^(r-2)=B/(Fintype.card V:ℝ)^(r-1) := by
      rw [div_div,←pow_succ',show r-2+1=r-1 by omega]
    rw [he];exact hφB C
  have hh:=ordinary_cycle_vertex_conflict_loss P r hr hn φ hφ (B/Fintype.card V)
    (div_nonneg hB hnR.le) hcoef D L hD v
  have h:= (ordinaryLocalPotential_sdiff_loss P Q F D T φ hφ v).trans hh
  convert h using 1 <;> ring

theorem ordinary_common_sdiff_bound (Q D : SimpleGraph V) (T S : Finset V) (L : ℝ)
    (hD : ∀ v,(D.degree v:ℝ)≤L) :
    |((common T S (fun v=>(Q\D).neighborFinset v)).card:ℝ)-
      (common T S (fun v=>Q.neighborFinset v)).card|≤S.card*L := by
  apply neighbourhood_stability
  intro v _
  have hsub : changed (Q.neighborFinset v) ((Q\D).neighborFinset v)⊆D.neighborFinset v := by
    intro w hw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset,
      SimpleGraph.sdiff_adj] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with h|h
    · exact not_not.mp (fun hn=>h.2 ⟨h.1,hn⟩)
    · exact (h.2 h.1.1).elim
  have hc : ((changed (Q.neighborFinset v) ((Q\D).neighborFinset v)).card:ℝ)≤D.degree v := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (SimpleGraph.card_neighborFinset_eq_degree _ _)
  exact hc.trans (hD v)

end Oberwolfach
