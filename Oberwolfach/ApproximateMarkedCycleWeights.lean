module

public import Oberwolfach.MarkedCycleWeights
public import Mathlib.Analysis.Normed.Group.Constructions

@[expose] public section

/-! Approximate coefficients on the fixed family of separated marked cycles.
Their error is an explicit typed-edge sup norm, with no density multiplier
applied to the removed weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1200000 in
theorem approximate_marked_cycle_coefficients {V E K : Type*}
    [Fintype V] [Nonempty V] [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V)
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (m : ℕ) (hm : 2≤m) (π : Equiv.Perm V) (b : ℕ)
    (hsep : ∀ e,¬PermutationClose π b (tail e) (head e))
    (hksep : ∀ e,¬PermutationClose π b (ktail e) (khead e))
    (f : Fin m → E → ℝ) (w : E → ℝ) (wK : K → ℝ) (hsum : ∀ e,(∑ j,f j e)=w e)
    (hf : ∀ j e,1/(2*(m:ℝ))≤f j e ∧ f j e≤2/(m:ℝ))
    (hwK : ∀ e,1/2≤wK e ∧ wK e≤3/2)
    (u : (Fin (m+1) → V) → ℝ) (hu : ∀ C,0≤u C)
    (he : ∀ i x y,(∑ C,if C i=x ∧ C (finRotate (m+1) i)=y then u C else 0)=
      copiedMarkedCapacity tail head ktail khead m f wK i x y)
    (B : ℝ) (hB : 0≤B) (hupper : ∀ C,u C≤B/(Fintype.card V:ℝ)^(m-1)) :
    ∃ q : MarkedCycleTuple tail head ktail khead m π b → ℝ,
      (∀ C,0≤q C ∧ q C≤B/(Fintype.card V:ℝ)^(m-1)) ∧
      ‖(∑ C,q C • markedCycleIncidence tail head ktail khead m C.val)-Sum.elim w wK‖≤
        (m:ℝ)*((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ) := by
  classical
  let a := copiedMarkedCapacity tail head ktail khead m f wK
  let q := separatedWeight π b u
  have hq (C : Fin (m+1) → V) : 0≤q C ∧ q C≤u C := separatedWeight_bounds π b u hu C
  have ha := (copiedMarkedCapacity_bounds tail head ktail khead hinj hkinj m (by omega) f wK hf hwK).1
  have hmr : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hs (C : Fin (m+1) → V) (hC : 0<q C) : IsMarkedCycleTuple tail head ktail khead m π b C := by
    obtain ⟨hsepC,_,hpos⟩ := separated_capacity_support π b a ha u hu
      (by
        intro i x y
        convert he i x y using 1
        apply Finset.sum_congr rfl
        intro C _
        split_ifs <;> rfl) C hC
    obtain ⟨hO,hK⟩ := (copied_marked_support_iff tail head ktail khead hinj hkinj m f wK
      (fun j e => (by positivity : (0:ℝ)<1/(2*m)).trans_le (hf j e).1)
      (fun e => by linarith [(hwK e).1]) C).mp hpos
    exact ⟨hsepC,hO,hK⟩
  refine ⟨fun C => q C.val,fun C => ⟨(hq C.val).1,(hq C.val).2.trans (hupper C.val)⟩,?_⟩
  rw [marked_cycle_weight_restriction tail head ktail khead m π b q (fun C => (hq C).1) hs]
  have hl := separated_marked_edge_loads tail head ktail khead hinj hkinj m hm π b hsep hksep
    f w wK hsum u hu he B hB hupper
  have hnonneg : 0≤((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ) := by positivity
  apply (pi_norm_le_iff_of_nonneg (show 0≤(m:ℝ)*((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ) by positivity)).mpr
  intro e
  simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs]
  cases e with
  | inl e => simpa only [q,mul_div_assoc,Sum.elim_inl] using hl.1 e
  | inr e =>
    have hh := hl.2 e
    have hmr1 : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
    have he : ((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ)≤
        (m:ℝ)*((m+1:ℝ)^2*(2*b+1)*B)/(Fintype.card V:ℝ) := by
      simpa only [one_mul,mul_div_assoc] using mul_le_mul_of_nonneg_right hmr1 hnonneg
    exact hh.trans he

end Oberwolfach
