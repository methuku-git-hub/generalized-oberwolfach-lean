module

public import Oberwolfach.TwoFactorMarkedPathIndependence

@[expose] public section
/-! The positions at multiples of c on two-edge-extended paths are independent. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem spaced_scaled_indices (c a b:ℕ) (hc:2≤c) (hab:a≠b):
    2+c*a+1≠2+c*b ∧ 2+c*b+1≠2+c*a := by
  rcases lt_or_gt_of_ne hab with h|h
  · have hm:=Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)
    have hh:c*a+c≤c*b := by nlinarith
    omega
  · have hm:=Nat.mul_le_mul_left c (Nat.succ_le_of_lt h)
    have hh:c*b+c≤c*a := by nlinarith
    omega

theorem two_factor_extended_markers_independent
    (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2)
    (s:Finset I) (u v:I→V) (P:∀ i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hlen:∀i∈s,(P i).length=c*d+4):
    let T:=fun _ : I => (Finset.range (d+1)).image (fun j=>2+c*j);
    ∀ x∈s.biUnion (fun i=>(T i).image (P i).getVert),
      ∀ y∈s.biUnion (fun i=>(T i).image (P i).getVert),¬F.Adj x y := by
  let T:I→Finset ℕ:=fun _=>(Finset.range (d+1)).image (fun j=>2+c*j)
  have hint:∀i∈s,∀a∈T i,0<a ∧ a<(P i).length := by
    intro i hi a ha
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp ha
    have hjd:j≤d := by simpa using hj
    have hm:=Nat.mul_le_mul_left c hjd
    rw [hlen i hi]
    omega
  have hspace:∀i∈s,∀a∈T i,∀b∈T i,a≠b→a+1≠b ∧ b+1≠a := by
    intro i hi a ha b hb hab
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hb
    have hjk:j≠k := by intro h;subst k;exact hab rfl
    exact spaced_scaled_indices c j k (by omega) hjk
  exact two_factor_spaced_path_vertices_independent F hF s u v P hp hP T hint hspace
end Oberwolfach
