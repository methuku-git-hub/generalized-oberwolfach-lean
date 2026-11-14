module

public import Oberwolfach.LongResidualPositivity
public import Oberwolfach.ConditionalCapacityPaths
public import Oberwolfach.ThreeIntervalSectorBounds

@[expose] public section

/-! Pointwise bounds for the same weights that recover every capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

set_option maxHeartbeats 800000 in
theorem long_capacity_sector_bounds {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (ha : ∀ i x y, 0≤a i x y) (hd : ∀ i x, 0<d i x)
    (hrow : ∀ i x, ∑ y, a i x y=d i x)
    (hcol : ∀ i y, ∑ x, a i x y=d (i+1) y)
    (M n a₀ a₁ d₀ d₁ : ℝ) (hn : (Fintype.card X : ℝ)=n) (hnpos : 0<n)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (hms : ∀ i, ∑ x, d i x=M)
    (hdscale : ∀ i x, d₀*n ≤ d i x ∧ d i x ≤ d₁*n)
    (s L : Fin 3 → ℕ) (hL : ∀ i, 0<L i)
    (hbd : ∀ i x, d (s i+L i) x=d (s (finRotate 3 i)) x)
    (hmix : ∀ i x z, |transitionWalk (capacityTransition a d) (s i) (L i) x z-
      capacityProfile d M (s i+L i) z| ≤ (1/10)*capacityProfile d M (s i+L i) z)
    (hres : ∀ (Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3))
      i j x y, pathEdgeLoad (longCapacityReserve a d s L Q i) j x y ≤ (11/27)*a (s i+j.val) x y)
    (Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3))
    (hfixed : ∀ i x z, Q.val i x z=walkTransport (threeIntervalMarginal (intervalDegrees d s L))
      (threeIntervalResidualSystem (intervalCapacities a s L) (intervalDegrees d s L)
        (longCapacityReserve a d s L) Q) (finRotate 3) (finRotate 3 i) 2 z x)
    (p : ∀ i, Fin (L i+1) → X)
    (hp : ∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0)
    (hap : ∀ i (j : Fin (L i)), a₀ ≤ a (s i+j.val) (p i j.castSucc) (p i j.succ) ∧
      a (s i+j.val) (p i j.castSucc) (p i j.succ) ≤ a₁) (c : Fin 3) :
    threeSectorCoefficient L (conditionalPathLower a₀ d₀ d₁) (halfResidualLower a₀ d₀ d₁)
      (d₁/3) c/n^((∑ i,L i)-2) ≤
      threeIntervalSector (intervalCapacities a s L) (intervalDegrees d s L) (longCapacityReserve a d s L) Q c p ∧
    threeIntervalSector (intervalCapacities a s L) (intervalDegrees d s L) (longCapacityReserve a d s L) Q c p ≤
      threeSectorCoefficient L (conditionalPathUpper a₁ d₀ d₁) (halfResidualUpper a₁ d₀ d₁)
        (d₀/3) c/n^((∑ i,L i)-2) := by
  let R := capacityTransition a d
  let A := intervalCapacities a s L
  let D := intervalDegrees d s L
  let ρ := longCapacityReserve a d s L
  have hT (i : Fin 3) (x z : X) : 0<transitionWalk R (s i) (L i) x z := by
    have hh := mixed_capacity_transition_scale d M n d₀ d₁ hn hnpos hd₀ hd₁ hms hdscale _ _ _ (hmix i x z)
    exact (by positivity : 0<((9/10)*(d₀/d₁))/n).trans_le hh.1
  have hK := long_residual_system_positive a d ha hd hrow hcol s L hL hbd hT hres Q
  have hR := capacityTransition_isTransition a d ha hd hrow
  have hD (i : Fin 3) (j : Fin (L i+1)) (x : X) : 0<D i j x := hd _ _
  have hA (i : Fin 3) (j : Fin (L i)) (x y : X) : 0≤A i j x y := ha _ _ _
  have hAr (i : Fin 3) (j : Fin (L i)) (x : X) : (∑ y,A i j x y)=D i j.castSucc x := hrow _ _
  have hAc (i : Fin 3) (j : Fin (L i)) (y : X) : (∑ x,A i j x y)=D i j.succ y := by
    simpa only [A,D,intervalCapacities,intervalDegrees,Fin.val_succ,Nat.add_assoc] using hcol (s i+j.val) y
  have hρ0 (i : Fin 3) (q : Fin (L i+1) → X) : 0≤ρ Q i q :=
    reservedPathWeight_nonneg R hR (s i) (L i) (Q.val i) (Q.property i (Set.mem_univ i)).1 q
  have hS (i : Fin 3) : halfResidualLower a₀ d₀ d₁ (L i)/n^(L i-1) ≤
        halfResidualPathWeight (A i) (D i) (ρ Q i) (p i) ∧
      halfResidualPathWeight (A i) (D i) (ρ Q i) (p i) ≤
        halfResidualUpper a₁ d₀ d₁ (L i)/n^(L i-1) :=
    half_residual_scale_bounds (hL i) (A i) (D i) (ρ Q i) (hA i) (hD i) (hAr i) (hAc i)
      (hρ0 i) (hres Q i) (p i) n a₀ a₁ d₀ d₁ hnpos ha₀ hd₀ (hap i)
      (fun j => hdscale _ _)
  let η := transitionPathWeight R (s c) (L c) (p c)/
    transitionWalk R (s c) (L c) (p c 0) (p c (Fin.last (L c)))
  have hηbounds : conditionalPathLower a₀ d₀ d₁ (L c)/n^(L c-1) ≤ η ∧
      η ≤ conditionalPathUpper a₁ d₀ d₁ (L c)/n^(L c-1) :=
    conditional_capacity_path_bounds a d M n a₀ a₁ d₀ d₁ hn hnpos ha₀ ha₁ hd₀ hd₁ hms hdscale
      (s c) (L c) (hL c) (p c) (hap c) (hmix c _ _)
  have hη : 0<η := (div_pos (conditionalPathLower_pos a₀ d₀ d₁ (L c) ha₀ hd₀ hd₁)
    (pow_pos hnpos _)).trans_le hηbounds.1
  have hρeq : ρ Q c (p c)=Q.val c (p c 0) (p c (Fin.last (L c)))*η := by
    unfold ρ longCapacityReserve reservedPathWeight η R
    ring
  have hm (i : Fin 3) (x : X) : 0<threeIntervalMarginal D i x := div_pos (hD i 0 x) (by norm_num)
  have hmb (i : Fin 3) : (d₀/3)*n ≤ threeIntervalMarginal D i (p i 0) ∧
      threeIntervalMarginal D i (p i 0) ≤ (d₁/3)*n := by
    have hh := hdscale (s i) (p i 0)
    change (d₀/3)*n ≤ d (s i+0) (p i 0)/3 ∧ d (s i+0) (p i 0)/3 ≤ (d₁/3)*n
    simp only [Nat.add_zero]
    constructor <;> linarith [hh.1,hh.2]
  exact three_interval_sector_scale_bounds A D ρ Q hm hK hfixed c p hp η hη hρeq n hnpos hL
    (conditionalPathLower a₀ d₀ d₁) (conditionalPathUpper a₁ d₀ d₁)
    (halfResidualLower a₀ d₀ d₁) (halfResidualUpper a₁ d₀ d₁) (d₀/3) (d₁/3)
    (fun k => conditionalPathLower_pos a₀ d₀ d₁ k ha₀ hd₀ hd₁)
    (fun k => halfResidualLower_pos a₀ d₀ d₁ k ha₀ hd₀ hd₁)
    (by positivity) hηbounds hS hmb

end Oberwolfach
