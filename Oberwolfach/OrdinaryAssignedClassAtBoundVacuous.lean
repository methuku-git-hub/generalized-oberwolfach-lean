module

public import Oberwolfach.OrdinaryAssignedClassAtBound
public import Oberwolfach.OrdinaryAssignedTriangleAtBound

@[expose] public section
/-! If the requested host degree exceeds the order, the corresponding
finite-order statement is vacuous; no upper-margin hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) vacuousFiniteEquality (n:ℕ):DecidableEq (Fin n):=Classical.decEq (Fin n)

theorem ordinary_assigned_class_at_bound_vacuous
    (m d K:ℕ) (hm:3≤m) (hd:2≤d)
    (θhost α ρ₀ s₀ ω βP ηP row ηH L:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (k:ℕ) (βH c B:ℝ) (N:ℕ) (hhigh:1<θhost+α):
    ordinaryAssignedClassAtBound m d K hm hd θhost α ρ₀ s₀ ω βP ηP row ηH L hρ₀ hs₀ k βH c B N := by
  intro n hn hn0 P D hreg hdeg
  let v:Fin n:=⟨0,hn0⟩
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hlt:(P.degree v:ℝ)<n:=by
    have hh:=P.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hgt:(n:ℝ)<(θhost+α)*n:=by nlinarith
  exact (not_le_of_gt (hlt.trans hgt) (hdeg v)).elim

theorem ordinary_assigned_triangle_at_bound_vacuous
    (d K:ℕ) (hd:2≤d)
    (θhost α ρ₀ s₀ ω βP ηP ηH L:ℝ) (hρ₀:0<ρ₀) (hs₀:0<s₀)
    (k:ℕ) (βH c B:ℝ) (N:ℕ) (hhigh:1<θhost+α):
    ordinaryAssignedTriangleAtBound d K hd θhost α ρ₀ s₀ ω βP ηP ηH L hρ₀ hs₀ k βH c B N := by
  intro n hn hn0 P D hreg hdeg
  let v:Fin n:=⟨0,hn0⟩
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hlt:(P.degree v:ℝ)<n:=by
    have hh:=P.degree_lt_card_verts v
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hgt:(n:ℝ)<(θhost+α)*n:=by nlinarith
  exact (not_le_of_gt (hlt.trans hgt) (hdeg v)).elim
end Oberwolfach
