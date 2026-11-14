module

public import Oberwolfach.PairedTupleRealizations

@[expose] public section

/-! Explicit absorber abundance from base-cycle and common-path abundance.
The only size conditions are the two displayed forbidden-label budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem polynomial_forbidden_label_margin (n β L : ℝ) (d : ℕ)
    (hn : 0≤n) (hd : 1≤d) (h : 2*L≤β*n) :
    L*n^(d-1)≤β/2*n^d := by
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg hn (d-1))
  have he : n^d=n^(d-1)*n := by
    nth_rw 1 [← Nat.sub_add_cancel hd]
    exact pow_succ _ _
  rw [he]
  nlinarith only [hh]

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {m : ℕ}

theorem paired_absorber_abundance (R : C → Finset V) (hm : 1≤m)
    (x : Fin (m+1) → V) (hx : Function.Injective x)
    (Base : (Fin (m+1) → V) → Prop)
    (Path : (Fin (m+1) → V) → ℕ → (Fin m → V) → Prop)
    (β : ℝ) (hβ : 0<β)
    (hbinj : ∀ y,Base y → Function.Injective y)
    (hb : ∀ y,Base y → ∃ C₀,R C₀=Finset.univ.image y)
    (hpaths : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ i : Fin (m+1),∀ g,Path y i.val g →
      (∃ C₀,R C₀=insert (y i) (Finset.univ.image g)) ∧
      (∃ C₁,R C₁=insert (x i) (Finset.univ.image g)))
    (hpinj : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ i<m+1,∀ g,Path y i g → Function.Injective g)
    (hbase : β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card {y // Base y})
    (hpath : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ i<m+1,β*(Fintype.card V:ℝ)^m≤Fintype.card {g // Path y i g})
    (hnbase : 2*(m+1:ℝ)^2≤β*Fintype.card V)
    (hnpath : 2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤β*Fintype.card V) :
    (β/2)^(m+2)*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
      Fintype.card (LabelledCycleRecord R (pairedAbsorberTemplate (m+1)).val (Finset.univ.image x)) := by
  let n : ℝ := Fintype.card V
  have hn : 0≤n := Nat.cast_nonneg _
  have hbm := polynomial_forbidden_label_margin n β ((m+1:ℝ)^2) (m+1) hn (by omega) hnbase
  have hpm := polynomial_forbidden_label_margin n β ((m:ℝ)*(2*(m+1)+(m+1)*m)) m hn hm (by nlinarith only [hnpath])
  have hchoices := pairedTupleChoice_count x Base Path
    (β/2*n^(m+1)) (β*n^m) (β/2*n^m) (by positivity)
    (by simpa only [Nat.add_sub_cancel] using (show β/2*n^(m+1)+(m+1:ℝ)^2*n^m≤Fintype.card {y // Base y} by
      have hh : (m+1:ℝ)^2*n^m≤β/2*n^(m+1) := by simpa only [Nat.add_sub_cancel] using hbm
      linarith [hbase]))
    hpath hpinj (by linarith [hpm])
  have he : (β/2*n^(m+1))*(β/2*n^m)^(m+1)=
      (β/2)^(m+2)*n^((m+1)*(m+1)) := by
    rw [mul_pow,← pow_mul]
    calc
      _ = ((β/2)*(β/2)^(m+1))*(n^(m+1)*n^(m*(m+1))) := by ring
      _ = (β/2)^((m+1)+1)*n^((m+1)+m*(m+1)) := by rw [pow_succ,pow_add];ring
      _ = _ := by congr 2 <;> ring
  rw [he] at hchoices
  exact hchoices.trans (by exact_mod_cast paired_absorber_count_from_choices R x hx Base Path hbinj hb hpaths)

end Oberwolfach
