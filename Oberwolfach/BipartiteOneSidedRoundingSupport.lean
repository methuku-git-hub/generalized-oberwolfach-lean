module

public import Oberwolfach.BipartiteDegreeRounding
public import Oberwolfach.CoordinateLocalLemma
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section
/-! Round a fractional bipartite edge selection with integer head demands
and integer tail upper bounds. One dummy edge per tail absorbs its fractional
slack; no independence of selected edges is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_one_sided_rounding_support {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e ∧ z e ≤ 1)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y)
    (hslack : ∀ x, 0 ≤ (f x:ℝ) - (∑ e, if tail e = x then z e else 0) ∧
      (f x:ℝ) - (∑ e, if tail e = x then z e else 0) ≤ 1) :
    ∃ D : E → Bool,
      (∀ x, (∑ e, if tail e = x ∧ D e = true then (1:ℕ) else 0) ≤ f x) ∧
      (∀ y, (∑ e, if head e = y ∧ D e = true then (1:ℕ) else 0) = g y) ∧
      (∀ e, z e=0 → D e=false) := by
  letI : DecidableEq (Y⊕Unit) := fun a b => Classical.propDecidable (a=b)
  let row : X → ℝ := fun x => ∑ e, if tail e = x then z e else 0
  have hr : (∑ x, row x) = ∑ e, z e := by
    dsimp [row]
    rw [Finset.sum_comm]
    simp
  have hc : (∑ y, (g y:ℝ)) = ∑ e, z e := by
    simp_rw [← hcol]
    rw [Finset.sum_comm]
    simp
  have hsum : (∑ y, (g y:ℝ)) ≤ ∑ x, (f x:ℝ) := by
    rw [hc, ← hr]
    apply Finset.sum_le_sum
    intro x _
    have hx := (hslack x).1
    dsimp only [row]
    linarith
  have hn : (∑ y, g y) ≤ ∑ x, f x := by exact_mod_cast hsum
  let gap : ℕ := (∑ x, f x) - ∑ y, g y
  have hgap : (∑ x, ((f x:ℝ) - row x)) = (gap:ℝ) := by
    rw [Finset.sum_sub_distrib, hr, ← hc]
    dsimp [gap]
    rw [Nat.cast_sub hn, Nat.cast_sum, Nat.cast_sum]
  let T : E⊕X → X := Sum.elim tail id
  let H : E⊕X → Y⊕Unit := Sum.elim (fun e => Sum.inl (head e)) (fun _ => Sum.inr ())
  let weight : E⊕X → ℝ := Sum.elim z (fun x => (f x:ℝ)-row x)
  let target : Y⊕Unit → ℕ := Sum.elim g (fun _ => gap)
  have hw : ∀ e, 0 ≤ weight e ∧ weight e ≤ 1 := by
    intro e
    cases e with
    | inl e => exact hz e
    | inr x => exact hslack x
  have hrow : ∀ x, (∑ e, if T e = x then weight e else 0) = f x := by
    intro x
    rw [Fintype.sum_sum_type]
    simp only [T,weight,Sum.elim_inl,Sum.elim_inr,id_eq]
    have hsingle : (∑ x':X, if x'=x then (f x':ℝ)-row x' else 0) = (f x:ℝ)-row x := by
      classical
      simpa only [Finset.mem_univ, ite_true] using (Finset.sum_ite_eq' (s:=Finset.univ) (a:=x) (b:=fun x':X => (f x':ℝ)-row x'))
    rw [hsingle]
    dsimp only [row]
    ring
  have hhead : ∀ y, (∑ e, if H e = y then weight e else 0) = target y := by
    intro y
    cases y with
    | inl y =>
      rw [Fintype.sum_sum_type]
      simp only [H,weight,target,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,
        Sum.inr_ne_inl,if_false,Finset.sum_const_zero,add_zero]
      exact hcol y
    | inr y =>
      cases y
      rw [Fintype.sum_sum_type]
      simp only [H,weight,target,Sum.elim_inl,Sum.elim_inr,Sum.inl_ne_inr,if_false,
        Finset.sum_const_zero,zero_add,Sum.inr.injEq,if_true]
      exact hgap
  obtain ⟨μ,hμ,hMarg⟩ := bipartite_degree_rounding T H f target weight hw hrow hhead
  have hp : 0 < μ.probability (fun _ => True) := by
    rw [finiteLaw_probability_true]
    norm_num
  obtain ⟨D,hD,_⟩ := finiteLaw_positive_event_exists μ (fun _ => True) hp
  obtain ⟨hDrow,hDcol⟩ := hμ D hD
  refine ⟨fun e=>D (Sum.inl e), ?_, ?_, ?_⟩
  · intro x
    have hh := hDrow x
    rw [Fintype.sum_sum_type] at hh
    simp only [T,Sum.elim_inl,Sum.elim_inr,id_eq] at hh
    have hle : (∑ e:E, if tail e=x ∧ D (Sum.inl e)=true then (1:ℕ) else 0) ≤ f x := by
      calc
        _ ≤ _ + (∑ e:X, if e=x ∧ D (Sum.inr e)=true then (1:ℕ) else 0) := Nat.le_add_right _ _
        _ = f x := hh
    exact hle
  · intro y
    have hh := hDcol (Sum.inl y)
    rw [Fintype.sum_sum_type] at hh
    simpa only [H,target,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,
      false_and,if_false,Finset.sum_const_zero,add_zero] using hh
  · intro e he
    by_contra hfalse
    have htrue : D (Sum.inl e) = true := by cases h : D (Sum.inl e) <;> simp_all
    have hm := finiteLaw_probability_mono μ (fun A=>A=D) (fun A=>A (Sum.inl e)=true)
      (by intro A hA; subst A; exact htrue)
    rw [finiteLaw_probability_point, hMarg (Sum.inl e)] at hm
    change μ.mass D ≤ z e at hm
    linarith
theorem bipartite_rounding_with_tail_ceilings_support {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E]
    (tail : E → X) (head : E → Y) (g : Y → ℕ) (z : E → ℝ)
    (hz : ∀ e, 0 ≤ z e ∧ z e ≤ 1)
    (hcol : ∀ y, (∑ e, if head e = y then z e else 0) = g y) :
    ∃ D : E → Bool,
      (∀ x, (∑ e, if tail e = x ∧ D e = true then (1:ℕ) else 0) ≤
        ⌈∑ e, if tail e = x then z e else 0⌉₊) ∧
      (∀ y, (∑ e, if head e = y ∧ D e = true then (1:ℕ) else 0) = g y) ∧
      (∀ e, z e=0 → D e=false) := by
  apply bipartite_one_sided_rounding_support tail head (fun x=>⌈∑ e, if tail e=x then z e else 0⌉₊) g z hz hcol
  intro x
  let a : ℝ := ∑ e, if tail e=x then z e else 0
  have ha : 0 ≤ a := by
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact (hz e).1
    · rfl
  have hlo := Nat.le_ceil a
  have hhi := Nat.ceil_lt_add_one ha
  change 0 ≤ ((⌈a⌉₊:ℕ):ℝ)-a ∧ ((⌈a⌉₊:ℕ):ℝ)-a ≤ 1
  constructor <;> linarith
end Oberwolfach
