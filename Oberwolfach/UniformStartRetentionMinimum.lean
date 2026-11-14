module

public import Oberwolfach.UniformStartRetention
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

/-! The retained size is the minimum of the actual start counts. The
same scalar approximation at every start bounds each deletion fraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [Nonempty V] [DecidableEq V] [DecidableEq U]

def startRetentionMinimum (A : V→Finset U) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun a=>(A a).card)

theorem startRetentionMinimum_le (A : V→Finset U) (a : V) :
    startRetentionMinimum A≤(A a).card := Finset.inf'_le _ (Finset.mem_univ a)

theorem startRetentionMinimum_eq_some (A : V→Finset U) :
    ∃ a,startRetentionMinimum A=(A a).card := by
  obtain ⟨a,_,h⟩ := Finset.exists_mem_eq_inf' (s:=Finset.univ) Finset.univ_nonempty (fun a=>(A a).card)
  exact ⟨a,h⟩

theorem startRetentionMinimum_close (A : V→Finset U) (μ E : ℝ)
    (h : ∀ a,|((A a).card:ℝ)-μ|≤E) :
    |(startRetentionMinimum A:ℝ)-μ|≤E := by
  obtain ⟨a,ha⟩ := startRetentionMinimum_eq_some A
  rw [ha];exact h a

theorem startRetentionMinimum_deletion_bound (A : V→Finset U) (μ E : ℝ)
    (h : ∀ a,|((A a).card:ℝ)-μ|≤E) (a : V) :
    (((A a).card-startRetentionMinimum A:ℕ):ℝ)≤2*E := by
  rw [Nat.cast_sub (startRetentionMinimum_le A a)]
  have h₁ := (abs_le.mp (h a)).2
  have h₂ := (abs_le.mp (startRetentionMinimum_close A μ E h)).1
  linarith

theorem startRetentionMinimum_deletion_fraction (A : V→Finset U) (μ E : ℝ)
    (hμ : 0<μ) (hE : 0≤E) (hsmall : E≤μ/2)
    (h : ∀ a,|((A a).card:ℝ)-μ|≤E) (a : V) :
    (((A a).card-startRetentionMinimum A:ℕ):ℝ)/(A a).card≤4*E/μ := by
  have hlo := (abs_le.mp (h a)).1
  have hcard : μ/2≤((A a).card:ℝ) := by linarith
  have hcpos : 0<((A a).card:ℝ) := lt_of_lt_of_le (by positivity) hcard
  have hd := startRetentionMinimum_deletion_bound A μ E h a
  apply (div_le_iff₀ hcpos).mpr
  have hr : 0≤4*E/μ := by positivity
  calc
    _ ≤ 2*E := hd
    _ = (4*E/μ)*(μ/2) := by field_simp;ring
    _ ≤ (4*E/μ)*(A a).card := mul_le_mul_of_nonneg_left hcard hr

end Oberwolfach
