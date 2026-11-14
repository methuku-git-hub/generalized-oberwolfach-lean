module

public import Oberwolfach.MarkedRootPaddingSizes

@[expose] public section

/-! Uniform numerical bounds for the marked transformer. Root-size bounds
precede the forbidden-set allowance and permutation separation radius. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem two_linear_exclusion_budgets (ρ σ ε C D:ℝ) (hρ:0<ρ) (hσ:0<σ)
    (hερ:ε≤ρ/2) (hεσ:ε≤σ/2) (hC:0≤C) (hD:0≤D) (f:ℕ):
    ∃ N:ℕ,1≤N∧∀ n:ℕ,N≤n→∀ W B:ℕ,(W:ℝ)≤ε*n+f→(B:ℝ)≤ε*n+f→
      (W:ℝ)+C<ρ*n∧(B:ℝ)+D<σ*n:=by
  obtain ⟨N₁,h₁⟩:=exists_nat_gt (2*((f:ℝ)+C+1)/ρ)
  obtain ⟨N₂,h₂⟩:=exists_nat_gt (2*((f:ℝ)+D+1)/σ)
  refine ⟨max 1 (max N₁ N₂),le_max_left _ _,?_⟩
  intro n hn W B hW hB
  have hn₁:(N₁:ℝ)≤n:=by exact_mod_cast (le_max_left N₁ N₂).trans ((le_max_right 1 _).trans hn)
  have hn₂:(N₂:ℝ)≤n:=by exact_mod_cast (le_max_right N₁ N₂).trans ((le_max_right 1 _).trans hn)
  have hlarge₁:=((div_lt_iff₀ hρ).mp (h₁.trans_le hn₁))
  have hlarge₂:=((div_lt_iff₀ hσ).mp (h₂.trans_le hn₂))
  have he₁:=mul_le_mul_of_nonneg_right hερ (Nat.cast_nonneg n)
  have he₂:=mul_le_mul_of_nonneg_right hεσ (Nat.cast_nonneg n)
  constructor <;> nlinarith only [hlarge₁,hlarge₂,he₁,he₂,hW,hB]

variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

theorem MarkedRootPair.padded_counts_bounded (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S)
    (r e:ℕ) (hr:(G.R∪G.R').card≤r) (he:Fintype.card A+Fintype.card S≤e):
    Fintype.card G.Exceptional≤e∧G.paddedRimCount≤e*(m+2)∧G.paddedSpokeCount≤e*(m+2)∧
      G.paddedRowBound≤r+2*e*m:=by
  have hi:Fintype.card G.Exceptional≤e:=(exceptional_marked_rows_card G.dst G.jr).trans (by omega)
  have ha:Fintype.card A≤e:=by omega
  have hs:Fintype.card S≤e:=by omega
  refine ⟨hi,(G.padded_rim_count_bound).trans (Nat.mul_le_mul_right _ ha),?_,?_⟩
  · change Fintype.card S+Fintype.card G.Exceptional*(m+1)≤e*(m+2)
    have hh:=Nat.mul_le_mul_right (m+1) hi
    nlinarith only [hs,hh]
  · change (G.R∪G.R').card+2*Fintype.card G.Exceptional*m≤r+2*e*m
    have hh:=Nat.mul_le_mul_right m (Nat.mul_le_mul_left 2 hi)
    omega

end Oberwolfach
