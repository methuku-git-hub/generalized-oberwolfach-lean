module

public import Oberwolfach.ThreeIntervalScaleAlgebra

@[expose] public section

/-! Bounds for a compatible three-interval path tuple after endpoint
cancellation. The coefficients are independent of the common class size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def threeSectorCoefficient (L : Fin 3 → ℕ) (u v : ℕ → ℝ) (d : ℝ) (c : Fin 3) : ℝ :=
  u (L c)*v (L (finRotate 3 c))*v (L (finRotate 3 (finRotate 3 c)))/d

theorem threeSectorCoefficient_pos (L : Fin 3 → ℕ) (u v : ℕ → ℝ) (d : ℝ)
    (hu : ∀ k, 0<u k) (hv : ∀ k, 0<v k) (hd : 0<d) (c : Fin 3) :
    0<threeSectorCoefficient L u v d c := by
  exact div_pos (mul_pos (mul_pos (hu _) (hv _)) (hv _)) hd

theorem three_interval_sector_scale_bounds {X : Type*} [Fintype X] {L : Fin 3 → ℕ}
    (a : ∀ i, Fin (L i) → X → X → ℝ) (d : ∀ i, Fin (L i+1) → X → ℝ)
    (ρ : transportProduct (threeIntervalMarginal d) (finRotate 3) → ∀ i, (Fin (L i+1) → X) → ℝ)
    (Q : transportProduct (threeIntervalMarginal d) (finRotate 3))
    (hm : ∀ i x, 0<threeIntervalMarginal d i x)
    (hK : ∀ i x z, 0<threeIntervalResidualSystem a d ρ Q i x z)
    (hfixed : ∀ i x z, Q.val i x z=walkTransport (threeIntervalMarginal d)
      (threeIntervalResidualSystem a d ρ Q) (finRotate 3) (finRotate 3 i) 2 z x)
    (c : Fin 3) (p : ∀ i, Fin (L i+1) → X)
    (hp : ∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0)
    (η : ℝ) (hη : 0<η)
    (hρ : ρ Q c (p c)=Q.val c (p c 0) (p c (Fin.last (L c)))*η)
    (n : ℝ) (hn : 0<n) (hL : ∀ i, 0<L i)
    (u₀ u₁ v₀ v₁ : ℕ → ℝ) (d₀ d₁ : ℝ)
    (hu₀ : ∀ k, 0<u₀ k) (hv₀ : ∀ k, 0<v₀ k) (hd₀ : 0<d₀)
    (hu : u₀ (L c)/n^(L c-1) ≤ η ∧ η ≤ u₁ (L c)/n^(L c-1))
    (hv : ∀ i, v₀ (L i)/n^(L i-1) ≤ halfResidualPathWeight (a i) (d i) (ρ Q i) (p i) ∧
      halfResidualPathWeight (a i) (d i) (ρ Q i) (p i) ≤ v₁ (L i)/n^(L i-1))
    (hd : ∀ i, d₀*n ≤ threeIntervalMarginal d i (p i 0) ∧
      threeIntervalMarginal d i (p i 0) ≤ d₁*n) :
    threeSectorCoefficient L u₀ v₀ d₁ c/n^((∑ i,L i)-2) ≤ threeIntervalSector a d ρ Q c p ∧
      threeIntervalSector a d ρ Q c p ≤ threeSectorCoefficient L u₁ v₁ d₀ c/n^((∑ i,L i)-2) := by
  rw [threeIntervalSector_formula a d ρ Q hm hK hfixed c p hp η hη hρ,
    fin3_product_erase,fin3_product_erase_twice]
  rw [← mul_assoc]
  have hh := three_path_scale_bounds n η
    (halfResidualPathWeight (a (finRotate 3 c)) (d (finRotate 3 c)) (ρ Q (finRotate 3 c)) (p (finRotate 3 c)))
    (halfResidualPathWeight (a (finRotate 3 (finRotate 3 c))) (d (finRotate 3 (finRotate 3 c)))
      (ρ Q (finRotate 3 (finRotate 3 c))) (p (finRotate 3 (finRotate 3 c))))
    (threeIntervalMarginal d (finRotate 3 (finRotate 3 c)) (p (finRotate 3 (finRotate 3 c)) 0))
    _ _ _ _ _ _ d₀ d₁ hn _ _ _ (hL c) (hL _) (hL _)
    (hu₀ _) (hv₀ _) (hv₀ _) hd₀ hu (hv _) (hv _) (hd _)
  rw [fin3_rotated_sum] at hh
  exact hh

end Oberwolfach
