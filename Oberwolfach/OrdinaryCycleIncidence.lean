module

public import Oberwolfach.OrdinaryCycleCountBounds
public import Oberwolfach.PositiveBoundedCoefficients

@[expose] public section

/-! The ordinary cycle incidence vectors use each physical cycle subgraph
once. Counting cycles through an edge bounds the positive baseline. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev OrdinaryCycle {V : Type*} (G : SimpleGraph V) (r : ℕ) :=
  {C : EmbeddedCycleFamily V r // C.val≤G}

def ordinaryCycleIncidence {V : Type*} (G : SimpleGraph V) (r : ℕ)
    (C : OrdinaryCycle G r) (e : G.edgeSet) : ℝ :=
  if e.val∈C.val.val.edgeSet then 1 else 0

theorem ordinaryCycleIncidence_nonneg {V : Type*} (G : SimpleGraph V) (r : ℕ)
    (C : OrdinaryCycle G r) (e : G.edgeSet) : 0≤ordinaryCycleIncidence G r C e := by
  dsimp [ordinaryCycleIncidence]
  split_ifs <;> norm_num

theorem ordinary_cycle_incidence_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (e : G.edgeSet) :
    (∑ C : OrdinaryCycle G r,ordinaryCycleIncidence G r C e)≤
      (r:ℝ)^2*(Fintype.card V:ℝ)^(r-2) := by
  apply (finite_subtype_sum_le (fun C : EmbeddedCycleFamily V r => C.val≤G)
    (fun C => if e.val∈C.val.edgeSet then (1:ℝ) else 0)
    (fun C => by split_ifs <;> norm_num)).trans
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := he
    have hh := ordinary_cycle_edge_count r u v huv.ne
    convert hh using 1
    apply Finset.sum_congr rfl
    intro C _
    simp only [SimpleGraph.mem_edgeSet]

theorem ordinary_cycle_positive_baseline {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (κ : ℝ) (hκ : 0<κ)
    (hn : 0<Fintype.card V) :
    ‖∑ C : OrdinaryCycle G r,
      ((κ/(4*(r:ℝ)^2))/(Fintype.card V:ℝ)^(r-2)) • ordinaryCycleIncidence G r C‖≤κ/4 := by
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hrr : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hp : 0<(Fintype.card V:ℝ)^(r-2) := pow_pos hnr _
  have hb : 0≤(κ/(4*(r:ℝ)^2))/(Fintype.card V:ℝ)^(r-2) := by positivity
  apply (pi_norm_le_iff_of_nonneg (show 0≤κ/4 by positivity)).mpr
  intro e
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply,smul_eq_mul,← Finset.mul_sum,Real.norm_eq_abs]
  have hs : 0≤∑ C : OrdinaryCycle G r,ordinaryCycleIncidence G r C e :=
    Finset.sum_nonneg (fun C _ => ordinaryCycleIncidence_nonneg G r C e)
  rw [abs_of_nonneg (mul_nonneg hb hs)]
  have hh := mul_le_mul_of_nonneg_left (ordinary_cycle_incidence_count G r e) hb
  have he : ((κ/(4*(r:ℝ)^2))/(Fintype.card V:ℝ)^(r-2))*
      ((r:ℝ)^2*(Fintype.card V:ℝ)^(r-2))=κ/4 := by field_simp
  exact he ▸ hh

theorem exact_positive_ordinary_cycle_weights {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (hr : 0<r) (hn : 0<Fintype.card V)
    (w : G.edgeSet → ℝ) (κ η B : ℝ) (hκ : 0<κ) (hη : η<κ/4)
    (hw : ‖w-(fun _ => (1:ℝ))‖≤κ/4)
    (happrox : ∀ w' : G.edgeSet → ℝ,‖w'-(fun _ => (1:ℝ))‖≤κ →
      ∃ a : OrdinaryCycle G r → ℝ,
        (∀ C,0≤a C ∧ a C≤B/(Fintype.card V:ℝ)^(r-2)) ∧
        ‖(∑ C,a C • ordinaryCycleIncidence G r C)-w'‖≤η) :
    ∃ a : OrdinaryCycle G r → ℝ,
      (∀ C,0<a C ∧ (κ/(4*(r:ℝ)^2))/(Fintype.card V:ℝ)^(r-2)≤a C ∧
        a C≤(κ/(4*(r:ℝ)^2)+B)/(Fintype.card V:ℝ)^(r-2)) ∧
      (∑ C,a C • ordinaryCycleIncidence G r C)=w := by
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hrr : (0:ℝ)<r := Nat.cast_pos.mpr hr
  obtain ⟨a,ha,he⟩ := subspace_positive_bounded_coefficients (⊤ : Submodule ℝ (G.edgeSet → ℝ))
    (ordinaryCycleIncidence G r) (fun _ => trivial) (fun _ => 1) w (by trivial)
    κ η (B/(Fintype.card V:ℝ)^(r-2)) ((κ/(4*(r:ℝ)^2))/(Fintype.card V:ℝ)^(r-2))
    hκ (by positivity) hη hw (ordinary_cycle_positive_baseline G r hr κ hκ hn)
    (fun w' _ hw' => happrox w' hw')
  refine ⟨a,?_,he⟩
  intro C
  obtain ⟨hp,hl,hu⟩ := ha C
  exact ⟨hp,hl,by simpa only [add_div] using hu⟩

end Oberwolfach
