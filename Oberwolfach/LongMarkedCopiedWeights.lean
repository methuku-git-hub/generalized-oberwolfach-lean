module

public import Oberwolfach.CopiedMarkedTransitions
public import Oberwolfach.LongCyclicCapacityTheorem
public import Oberwolfach.CycleWeightExtension

@[expose] public section

/-! Uniform cycle weights for the copied marked graph. The constants precede
all graph data and capacity choices. The ordinary positions share the same
underlying directed graph; the last interface alone is exceptional. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1400000 in
theorem long_marked_copied_weights (α p₀ : ℝ) (hα : 0<α) (hαmax : α≤1)
    (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (t k : ℕ)
    (ht : 1+3*⌈Real.log (10*(100/p₀+1))/(-Real.log (1-α/200))⌉₊≤t)
    (hc : 12*t+4≤k+2) :
    ∃ b₀ b₁ : ℝ,0<b₀ ∧ 0<b₁ ∧
    ∀ (V : Type u) (E : Type v) (K : Type w)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V],
    ∀ (tail head : E → V) (ktail khead : K → V),
    Function.Injective (fun e => (tail e,head e)) →
    Function.Injective (fun e => (ktail e,khead e)) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → 0<Fintype.card V → 10/p₀≤(Fintype.card V:ℝ) →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    ∀ (f : Fin (k+1) → E → ℝ) (wK : K → ℝ) (d : Fin (k+2) → V → ℝ),
    (∀ j e,1/(2*(k+1:ℝ))≤f j e ∧ f j e≤2/(k+1:ℝ)) →
    (∀ e,1/2≤wK e ∧ wK e≤3/2) →
    (∀ j x,(9/10)*(p*D/(k+1:ℝ))≤d j x ∧ d j x≤(11/10)*(p*D/(k+1:ℝ))) →
    (∀ j,(∑ x,d j x)=∑ x,d 0 x) →
    (∀ j x,occurrenceSumLinear tail (f j) x=d j.castSucc x) →
    (∀ j x,occurrenceSumLinear head (f j) x=d j.succ x) →
    (∀ x,occurrenceSumLinear ktail wK x=d (Fin.last (k+1)) x) →
    (∀ x,occurrenceSumLinear khead wK x=d 0 x) →
    (∀ x y,x≠y → α*p^2*Fintype.card V ≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    let a := copiedMarkedCapacity tail head ktail khead (k+1) f wK
    ∃ wC : (Fin (k+2) → V) → ℝ,
      (∀ C,0≤wC C) ∧
      (∀ i x y,(∑ C,if C i=x ∧ C (finRotate (k+2) i)=y then wC C else 0)=a i x y) ∧
      (∀ C,wC C≤b₁/(Fintype.card V:ℝ)^k) ∧
      (∀ C,(∀ i,0<a i (C i) (C (finRotate (k+2) i))) → b₀/(Fintype.card V:ℝ)^k≤wC C) := by
  have hmix : 0<α/200 := by positivity
  have hmix1 : α/200<1 := by linarith
  have hB : 1≤100/p₀ := (le_div_iff₀ hp₀).mpr (by linarith)
  obtain ⟨b₀,b₁,hb₀,hb₁,hweights⟩ := long_cyclic_capacity_theorem
    (α/200) (100/p₀) (1/(2*(k+1:ℝ))) 2 (p₀/(3*(k+1:ℝ))) (2/(k+1:ℝ))
    hmix hmix1 hB (by positivity) (by norm_num) (by positivity) (by positivity) t ht (k+2) hc
  refine ⟨b₀,b₁,hb₀,hb₁,?_⟩
  intro V E K instV instE instK instDec tail head ktail khead hinj hkinj p D hp hpmax hn hsize hDlo hDhi f wK d hf hwK hd htotal hfr hfc hkr hkc hcommon
  classical
  let a := copiedMarkedCapacity tail head ktail khead (k+1) f wK
  obtain ⟨ha,hapos⟩ := copiedMarkedCapacity_bounds tail head ktail khead hinj hkinj
    (k+1) (by omega) f wK (by simpa only [Nat.cast_add,Nat.cast_one] using hf) hwK
  obtain ⟨hrow,hcol⟩ := copiedMarkedCapacity_balance tail head ktail khead (k+1) f wK d hfr hfc hkr hkc
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hdscale (i : Fin (k+2)) (x : V) :
      (p₀/(3*(k+1:ℝ)))*Fintype.card V≤d i x ∧ d i x≤(2/(k+1:ℝ))*Fintype.card V :=
    marked_capacity_degree_scales k p p₀ D (Fintype.card V) (d i x) hp₀ hp hpmax hnr hDlo hDhi (hd i x)
  obtain ⟨hupper,hminor⟩ := copied_marked_transition_hypotheses tail head ktail khead hinj hkinj
    k f wK d α p p₀ D hα hp₀ hp hpmax hn hsize hDlo hDhi hf hwK hd htotal hrow hcommon
  obtain ⟨wC,hwC,he,hbounds⟩ := hweights (Fintype.card V) hn V rfl a d ha hrow hcol
    (by simpa only [Nat.cast_add,Nat.cast_one] using hapos) hdscale {Fin.last (k+1)} (by simp)
    (by
      intro i hi x y
      have hh := hupper i (by simpa only [Finset.mem_singleton] using hi) x y
      convert hh using 1 <;> simp only [Fin.mk_zero])
    (by
      intro i hi hi1 hi2 x z
      have hh := hminor i (by simpa only [Finset.mem_singleton] using hi)
        (by simpa only [Finset.mem_singleton] using hi1) (by simpa only [Finset.mem_singleton] using hi2) x z
      convert hh using 1 <;> simp only [Fin.mk_zero])
  refine ⟨cycleWeightExtend a wC,cycleWeightExtend_nonneg a wC (fun C => (hwC C).le),?_,?_,?_⟩
  · intro i x y
    have hh := (cycleWeightExtend_edge a wC i x y).trans (he i x y)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> rfl
  · intro C
    apply cycleWeightExtend_upper a wC _ (by positivity) _ C
    intro C
    simpa only [Nat.add_sub_cancel] using (hbounds C).2
  · intro C hC
    change ∀ i,0<a i (C i) (C (finRotate (k+2) i)) at hC
    change b₀/(Fintype.card V:ℝ)^k≤cycleWeightExtend a wC C
    rw [cycleWeightExtend,dif_pos hC]
    simpa only [Nat.add_sub_cancel] using (hbounds ⟨C,hC⟩).1

end Oberwolfach
