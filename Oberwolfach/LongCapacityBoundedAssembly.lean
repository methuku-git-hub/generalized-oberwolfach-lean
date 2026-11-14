module

public import Oberwolfach.LongCapacityMixingReserve
public import Oberwolfach.LongCapacityPointwiseBounds

@[expose] public section

/-! Exact edge equations and uniform positive path-tuple weights are obtained
simultaneously from the same fixed point. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longCycleLower (L : Fin 3 → ℕ) (a₀ d₀ d₁ : ℝ) : ℝ :=
  ∑ c,threeSectorCoefficient L (conditionalPathLower a₀ d₀ d₁) (halfResidualLower a₀ d₀ d₁) (d₁/3) c

def longCycleUpper (L : Fin 3 → ℕ) (a₁ d₀ d₁ : ℝ) : ℝ :=
  ∑ c,threeSectorCoefficient L (conditionalPathUpper a₁ d₀ d₁) (halfResidualUpper a₁ d₀ d₁) (d₀/3) c

theorem longCycleLower_pos (L : Fin 3 → ℕ) (a₀ d₀ d₁ : ℝ)
    (ha₀ : 0<a₀) (hd₀ : 0<d₀) (hd₁ : 0<d₁) : 0<longCycleLower L a₀ d₀ d₁ := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro c _
  exact threeSectorCoefficient_pos L _ _ _
    (fun k => conditionalPathLower_pos a₀ d₀ d₁ k ha₀ hd₀ hd₁)
    (fun k => halfResidualLower_pos a₀ d₀ d₁ k ha₀ hd₀ hd₁) (by positivity) c

theorem longCycleUpper_pos (L : Fin 3 → ℕ) (a₁ d₀ d₁ : ℝ)
    (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁) : 0<longCycleUpper L a₁ d₀ d₁ := by
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro c _
  exact threeSectorCoefficient_pos L _ _ _
    (fun k => conditionalPathUpper_pos a₁ d₀ d₁ k ha₁ hd₀ hd₁)
    (fun k => halfResidualUpper_pos a₁ d₀ d₁ k ha₁ hd₀ hd₁) (by positivity) c

set_option maxHeartbeats 800000 in
theorem long_capacity_bounded_interval_weights {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (ha : ∀ i x y, 0 ≤ a i x y) (hd : ∀ i x, 0 < d i x)
    (hrow : ∀ i x, ∑ y, a i x y=d i x)
    (hcol : ∀ i y, ∑ x, a i x y=d (i+1) y)
    (M : ℝ) (hM : 0 < M) (hms : ∀ i, ∑ x, d i x=M)
    (s L : Fin 3 → ℕ) (t : ℕ)
    (hbd : ∀ i x, d (s i+L i) x=d (s (finRotate 3 i)) x)
    (J : Finset ℕ) (hJ : J.card ≤ 1) (κ B : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hB : 1 ≤ B)
    (ht : 1+3*⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊ ≤ t)
    (hL : ∀ i, 4*t+1 ≤ L i)
    (hupper : ∀ i j, s i ≤ j → j < s i+L i → j ∉ J → ∀ x y,
      capacityTransition a d j x y ≤ B*capacityProfile d M (j+1) y)
    (hminor : ∀ i j, s i ≤ j → j+3 ≤ s i+L i → j ∉ J → j+1 ∉ J → j+2 ∉ J →
      ∀ x y, κ*capacityProfile d M (j+3) y ≤ transitionWalk (capacityTransition a d) j 3 x y)
    (n a₀ a₁ d₀ d₁ : ℝ) (hn : (Fintype.card X : ℝ)=n) (hnpos : 0<n)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hdscale : ∀ i x, d₀*n ≤ d i x ∧ d i x ≤ d₁*n) :
    ∃ ω : (∀ i,Fin (L i+1) → X) → ℝ,
      (∀ p,0≤ω p) ∧ (∑ p,ω p)=M ∧
      (∀ (i : Fin 3) (j : Fin (L i)) (x y : X),
        (∑ p,if p i j.castSucc=x ∧ p i j.succ=y then ω p else 0)=a (s i+j.val) x y) ∧
      (∀ p,0<ω p → ∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0) ∧
      (∀ p,(∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0) →
        (∀ i (j : Fin (L i)),a₀ ≤ a (s i+j.val) (p i j.castSucc) (p i j.succ) ∧
          a (s i+j.val) (p i j.castSucc) (p i j.succ) ≤ a₁) →
        longCycleLower L a₀ d₀ d₁/n^((∑ i,L i)-2) ≤ ω p ∧
          ω p ≤ longCycleUpper L a₁ d₀ d₁/n^((∑ i,L i)-2)) := by
  obtain ⟨Q,ω,hω0,hωM,hωedge,hωsupp,hfixed,hformula⟩ :=
    long_capacity_interval_assembly a d ha hd hrow hcol M hM hms s L t hbd J hJ κ B hκ hκ1 hB ht hL hupper hminor
  obtain ⟨hmix,hres⟩ := long_capacity_mixing_reserve a d ha hd hrow hcol M hM hms s L t hbd J hJ κ B hκ hκ1 hB ht hL hupper hminor
  refine ⟨ω,hω0,hωM,hωedge,hωsupp,?_⟩
  intro p hp hap
  have hb (c : Fin 3) := long_capacity_sector_bounds a d ha hd hrow hcol M n a₀ a₁ d₀ d₁
    hn hnpos ha₀ ha₁ hd₀ hd₁ hms hdscale s L (fun i => by have := hL i;omega) hbd
    hmix hres Q hfixed p hp hap c
  have hlo := Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => (hb c).1)
  have hup := Finset.sum_le_sum (fun c (_ : c∈Finset.univ) => (hb c).2)
  rw [← Finset.sum_div] at hlo hup
  rw [hformula p hp]
  exact ⟨hlo,hup⟩

end Oberwolfach
