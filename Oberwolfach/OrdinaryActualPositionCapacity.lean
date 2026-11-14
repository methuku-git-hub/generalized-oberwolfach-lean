module

public import Oberwolfach.OrdinaryAssignedCapacityCeiling

@[expose] public section
/-! The exact natural-number ceiling in the assignment lemma satisfies the
position capacity under the ordinary caller's displayed numerical bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_actual_position_capacity
    (n θ C ε lam d a A Z E:ℝ) (hn:0<n) (hθ:0≤θ) (hC:1≤C)
    (hε:0≤ε) (hlam:0≤lam) (hd:0<d) (ha:0<a) (hE0:0≤E)
    (hearly:C*(ε+ε^2/a)≤1/100000)
    (hlate:C/d+C*lam+C*lam/a≤θ/100000)
    (hA:A≤(2/d+lam)*n) (hZ:Z≤(2*θ*ε+2*lam)*n)
    (hE:E≤C*(θ*ε^2+lam*ε)*n^2+C*d*n)
    (hlarge:8*(4*C*d/a+1)+10≤θ*n/16):
    8*A+8*((⌈4*E/(a*n)⌉₊:ℕ):ℝ)+4*Z+10≤θ*n/4 := by
  have hv:=ordinary_assigned_ceiling_bound n θ C ε lam a d E hn ha hE0 hE
  apply ordinary_position_capacity_from_displayed_bounds n θ C ε lam (1/d) (1/a) A Z
    ((⌈4*E/(a*n)⌉₊:ℕ):ℝ) (4*C*d/a+1) hn.le hθ hC hε hlam (by positivity) (by positivity)
  · convert hearly using 1 <;> ring
  · convert hlate using 1 <;> ring
  · convert hA using 1 <;> ring
  · exact hZ
  · exact hv
  · exact hlarge
end Oberwolfach
