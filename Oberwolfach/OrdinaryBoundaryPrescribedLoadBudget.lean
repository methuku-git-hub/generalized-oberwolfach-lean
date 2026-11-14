module

public import Oberwolfach.PrescribedBoundaryMatchingLoadBudget

@[expose] public section
/-! Boundary starts and unmatched physical rows supply the prescribed-load
input at a spacing chosen independently of the wheel-length threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_prescribed_load_budget
    (n h d:ℕ) (δ a γ:ℝ) (hd:0<d) (hδ:0≤δ) (hhn:h≤n)
    (hD:4/(d:ℝ)≤δ/16)
    (hN:4*(n:ℝ)^(3/4:ℝ)≤δ*n/16)
    (hMatching:2*((max a γ)*n)≤δ*n/8)
    (prescribed bad:Fin n→ℝ)
    (hpres:∀v,prescribed v≤4*(h:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)+2*((max a γ)*n))
    (hbad:∀v,bad v≤δ*n/8):
    ∀v,prescribed v+bad v≤δ*n/2 :=by
  intro v
  have hd':0<(d:ℝ):=by exact_mod_cast hd
  have hh':(h:ℝ)≤n:=by exact_mod_cast hhn
  have hn:0≤(n:ℝ):=by positivity
  have hz:0≤(δ/2)*(n:ℝ)/4:=by positivity
  have hb:=prescribed_boundary_matching_load_budget n h (d:ℝ) (δ/2) a γ n hd' hh'
    (by linarith) (by linarith) (by linarith) (prescribed v) (bad v) 0 (hpres v) (by linarith [hbad v]) hz
  linarith only [hb]
end Oberwolfach
