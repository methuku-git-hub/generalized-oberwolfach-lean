module

public import Oberwolfach.HypergraphColourCliques
public import Oberwolfach.NeighbourhoodLocalLemma

@[expose] public section

/-! Fixed indices and base coordinate sets for all list and colour-degree
requirements in one round. Only the designated real edges are counted;
auxiliary edges may still affect their colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def realColourClass {V E C : Type*}
    (R : E → Finset V) (L : E → Finset C) (H : Finset E) (v : V) (c : C) : Finset E :=
  H.filter (fun e=>v∈R e ∧ c∈L e)

abbrev ColourRoundTest (V C : Type*) {E : Type*} (H : Finset E) :=
  {e // e∈H} ⊕ (V×C)

def colourRoundBase {V E C : Type*} (R : E → Finset V) (L : E → Finset C) (H : Finset E) :
    ColourRoundTest V C H → Finset E
  | .inl e => {e.val}
  | .inr p => realColourClass R L H p.1 p.2

theorem realColourClass_subset {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E) (v : V) (c : C) :
    realColourClass R L H v c⊆hypergraphColourClique R L v c := by
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩

theorem colourRoundBase_card {V E C : Type*} [Fintype E]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E) {s : ℕ} (hs : 1≤s)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (i : ColourRoundTest V C H) : (colourRoundBase R L H i).card≤s := by
  cases i with
  | inl e => simpa only [colourRoundBase,Finset.card_singleton] using hs
  | inr p => exact (Finset.card_le_card (realColourClass_subset R L H p.1 p.2)).trans (hdegree p.1 p.2)

theorem colourRoundBase_incidence
    {V E C : Type*} [Fintype V] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E) {k l : ℕ}
    (hsize : ∀ e,(R e).card≤k) (hcard : ∀ e,(L e).card=l) (e : E) :
    (Finset.univ.filter (fun i : ColourRoundTest V C H=>e∈colourRoundBase R L H i)).card≤1+k*l := by
  classical
  have hleft : (∑ f : {f // f∈H},if e=f.val then (1 : ℕ) else 0)≤1 := by
    by_cases he : e∈H
    · have hh (f : {f // f∈H}) : e=f.val ↔ f=⟨e,he⟩ := by
        constructor
        · intro h;exact Subtype.ext h.symm
        · intro h;exact (congrArg Subtype.val h).symm
      simp_rw [hh]
      simp
    · have hh (f : {f // f∈H}) : e≠f.val := fun h=>he (h.symm ▸ f.property)
      simp only [hh,ite_false,Finset.sum_const_zero,Nat.zero_le]
  have hright : (∑ p : V×C,if e∈realColourClass R L H p.1 p.2 then (1 : ℕ) else 0)≤k*l := by
    rw [Fintype.sum_prod_type]
    by_cases he : e∈H
    · simp only [realColourClass,Finset.mem_filter,he,true_and,ite_and]
      simp_rw [Finset.sum_ite_irrel,Finset.sum_const_zero]
      have hcount : (∑ v : V,if v∈R e then ∑ c : C,if c∈L e then (1 : ℕ) else 0 else 0)=
          (R e).card*(L e).card := by
        simp
      rw [hcount,hcard]
      exact Nat.mul_le_mul_right _ (hsize e)
    · simp only [realColourClass,Finset.mem_filter,he,false_and,ite_false,Finset.sum_const_zero]
      exact Nat.zero_le _
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fintype.sum_sum_type]
  simp only [colourRoundBase,Finset.mem_singleton]
  exact add_le_add hleft hright

end Oberwolfach
