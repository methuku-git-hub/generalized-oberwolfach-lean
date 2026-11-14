module

public import Oberwolfach.OrdinaryActualPositionCapacity

@[expose] public section
/-! The finite tail and ceiling in the prescribed-position inequality are
absorbed by one order threshold chosen from the fixed constants. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_position_capacity_for_large_orders
    (θ C ε lam d a:ℝ) (hθ:0<θ) (hC:1≤C)
    (hε:0≤ε) (hlam:0≤lam) (hd:0<d) (ha:0<a)
    (hearly:C*(ε+ε^2/a)≤1/100000)
    (hlate:C/d+C*lam+C*lam/a≤θ/100000):
    ∃ N:ℕ,∀ n:ℕ,N≤n→0<n→∀ A Z E:ℝ,
      0≤E→A≤(2/d+lam)*n→Z≤(2*θ*ε+2*lam)*n→
      E≤C*(θ*ε^2+lam*ε)*(n:ℝ)^2+C*d*n→
      8*A+8*((⌈4*E/(a*n)⌉₊:ℕ):ℝ)+4*Z+10≤θ*n/4 := by
  obtain ⟨N,hN⟩:=exists_nat_ge (16*(8*(4*C*d/a+1)+10)/θ)
  refine ⟨N,?_⟩
  intro n hn hn0 A Z E hE0 hA hZ hE
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hbound:16*(8*(4*C*d/a+1)+10)/θ≤(n:ℝ):=
    hN.trans (by exact_mod_cast hn)
  have hlarge:8*(4*C*d/a+1)+10≤θ*(n:ℝ)/16:=by
    have hh:16*(8*(4*C*d/a+1)+10)≤(n:ℝ)*θ:=(div_le_iff₀ hθ).mp hbound
    linarith
  exact ordinary_actual_position_capacity n θ C ε lam d a A Z E hnR hθ.le hC hε hlam hd ha hE0 hearly hlate hA hZ hE hlarge
end Oberwolfach
