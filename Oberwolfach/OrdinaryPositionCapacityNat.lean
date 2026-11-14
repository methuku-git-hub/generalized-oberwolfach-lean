module

public import Oberwolfach.OrdinaryPositionCapacityEventually

@[expose] public section
/-! Convert the ordinary caller's real estimates to the exact natural-number
capacity required by the position selection theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_natural_position_capacity_for_large_orders
    (θ C ε lam d a:ℝ) (hθ:0<θ) (hC:1≤C)
    (hε:0≤ε) (hlam:0≤lam) (hd:0<d) (ha:0<a)
    (hearly:C*(ε+ε^2/a)≤1/100000)
    (hlate:C/d+C*lam+C*lam/a≤θ/100000):
    ∃ N:ℕ,∀ n:ℕ,N≤n→0<n→∀ A Z E R:ℕ,
      (A:ℝ)≤(2/d+lam)*n→(Z:ℝ)≤(2*θ*ε+2*lam)*n→
      (E:ℝ)≤C*(θ*ε^2+lam*ε)*(n:ℝ)^2+C*d*n→
      θ*n/4≤(R:ℝ)→
      8*A+8*⌈4*(E:ℝ)/(a*n)⌉₊+4*Z+10≤R := by
  obtain ⟨N,hN⟩:=ordinary_position_capacity_for_large_orders θ C ε lam d a hθ hC hε hlam hd ha hearly hlate
  refine ⟨N,?_⟩
  intro n hn hn0 A Z E R hA hZ hE hR
  have h:=hN n hn hn0 A Z E (by positivity) hA hZ hE
  have hh:8*(A:ℝ)+8*((⌈4*(E:ℝ)/(a*n)⌉₊:ℕ):ℝ)+4*(Z:ℝ)+10≤R:=h.trans hR
  exact_mod_cast hh
end Oberwolfach
