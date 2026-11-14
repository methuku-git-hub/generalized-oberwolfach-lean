module

public import Oberwolfach.BoundedBipartiteFractionalMatching
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! Symmetrisation of the bipartite weighting gives the bounded perfect
fractional matching required by ordinary triangle cover-down. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bounded_matrix_fractional_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (M : V → V → ℕ) (hM : ∀ x y, M x y ≤ 1)
    (β : ℝ) (hβ : 0<β) (hβhalf : β<1/2) (hn : 0<Fintype.card V)
    (hrow : ∀ x, (1/2+β)*Fintype.card V ≤ ((∑ y, M x y : ℕ) : ℝ))
    (hcol : ∀ y, (1/2+β)*Fintype.card V ≤ ((∑ x, M x y : ℕ) : ℝ)) :
    ∃ z : V → V → ℝ,
      (∀ x y, M x y=0 → z x y=0) ∧
      (∀ x y, M x y=1 → β/(5*Fintype.card V) ≤ z x y ∧
        z x y ≤ 5/(β*Fintype.card V)) ∧
      (∀ x, ∑ y, z x y=1) ∧ (∀ y, ∑ x, z x y=1) := by
  obtain ⟨w,hw,hl,hr⟩ := bounded_bipartite_fractional_matching M hM β hβ hβhalf hn hrow hcol
  let z (x y : V) : ℝ := ∑ i : Fin (M x y), w ⟨x,y,i⟩
  refine ⟨z,?_,?_,?_,?_⟩
  · intro x y hzero
    apply Finset.sum_eq_zero
    intro i _
    have hi := i.isLt
    omega
  · intro x y hone
    constructor
    · have hh := Finset.sum_le_sum (fun (i : Fin (M x y)) (_ : i∈Finset.univ) => (hw ⟨x,y,i⟩).1)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,hone,Nat.cast_one,one_nsmul] using hh
    · have hh := Finset.sum_le_sum (fun (i : Fin (M x y)) (_ : i∈Finset.univ) => (hw ⟨x,y,i⟩).2)
      simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,hone,Nat.cast_one,one_nsmul] using hh
  · intro x
    have hh := hl x
    rw [Fintype.sum_sigma] at hh
    have he (u : V) : (∑ e : (Σ y, Fin (M u y)),
        if u=x then w ⟨u,e⟩ else 0)=if u=x then ∑ y, z u y else 0 := by
      by_cases h : u=x
      · subst u
        simp only [ite_true,Fintype.sum_sigma,z]
      · simp [h]
    simp_rw [he] at hh
    simpa using hh
  · intro y
    have hh := hr y
    rw [Fintype.sum_sigma] at hh
    have he (x : V) : (∑ e : (Σ v, Fin (M x v)),
        if e.1=y then w ⟨x,e⟩ else 0)=z x y := by
      rw [Fintype.sum_sigma]
      have he' (v : V) : (∑ i : Fin (M x v),
          if v=y then w ⟨x,v,i⟩ else 0)=if v=y then z x v else 0 := by
        by_cases h : v=y
        · subst v
          simp only [ite_true,z]
        · simp [h]
      simp_rw [he']
      simp
    simpa only [he] using hh

/-- The coefficient of an unordered graph edge is represented by a symmetric
function of its endpoints, zero on nonedges. Every vertex has total load one. -/
theorem bounded_perfect_fractional_matching
    {V : Type*} [Fintype V] (Q : SimpleGraph V) (β : ℝ)
    (hβ : 0<β) (hβhalf : β<1/2)
    (hn : 4/β ≤ (Fintype.card V : ℝ))
    (hdegree : ∀ v, (1/2+β)*Fintype.card V ≤ (Q.degree v : ℝ)) :
    ∃ w : V → V → ℝ,
      (∀ u v, w u v=w v u) ∧
      (∀ u v, ¬ Q.Adj u v → w u v=0) ∧
      (∀ u v, Q.Adj u v → β/(5*Fintype.card V) ≤ w u v ∧
        w u v ≤ 5/(β*Fintype.card V)) ∧
      (∀ v, ∑ u, w v u=1) := by
  classical
  let M (x y : V) : ℕ := if Q.Adj x y then 1 else 0
  have hM (x y : V) : M x y≤1 := by dsimp [M];split_ifs <;> omega
  have hrow (x : V) : ∑ y, M x y=Q.degree x := by
    rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,Finset.card_filter]
  have hcol (y : V) : ∑ x, M x y=Q.degree y := by
    rw [← hrow y]
    apply Finset.sum_congr rfl
    intro x _
    simp only [M,Q.adj_comm]
  have hnpos : 0<Fintype.card V := by
    have hh : (0 : ℝ)<Fintype.card V := lt_of_lt_of_le (div_pos (by norm_num) hβ) hn
    exact_mod_cast hh
  obtain ⟨z,hzero,hbound,hl,hr⟩ := bounded_matrix_fractional_matching M hM β hβ hβhalf hnpos
    (fun x => by rw [hrow];exact hdegree x)
    (fun y => by rw [hcol];exact hdegree y)
  refine ⟨fun u v => (z u v+z v u)/2,?_,?_,?_,?_⟩
  · intro u v;ring
  · intro u v huv
    dsimp only
    rw [hzero u v (by simp [M,huv]),hzero v u (by simp [M,Q.adj_comm,huv])]
    norm_num
  · intro u v huv
    have h₁ := hbound u v (by simp [M,huv])
    have h₂ := hbound v u (by simp [M,huv.symm])
    constructor <;> linarith
  · intro v
    rw [← Finset.sum_div,Finset.sum_add_distrib,hl,hr]
    norm_num

end Oberwolfach
