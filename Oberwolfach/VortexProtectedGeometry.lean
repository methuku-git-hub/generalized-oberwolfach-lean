module

public import Oberwolfach.VortexSizeBounds

@[expose] public section

/-! The sizes needed for protected cover-down follow from the actual paired
vortex, including the final step whose deeper pair is empty. The vertex and
index sizes retain their separate floor recurrences. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.extended_successor_size_bounds
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0 ≤ ε) (i : ℕ) :
    ((Q.extendedVertices (i+1)).card : ℝ) ≤ ε * (Q.extendedVertices i).card ∧
    ((Q.extendedIndices (i+1)).card : ℝ) ≤ ε * (Q.extendedIndices i).card := by
  by_cases hi : i+1 ≤ Q.length
  · rw [Q.extendedVertices_eq hi, Q.extendedVertices_eq (by omega : i ≤ Q.length),
      Q.extendedIndices_eq hi, Q.extendedIndices_eq (by omega : i ≤ Q.length)]
    constructor
    · rw [Q.sizes (i+1) hi, floorOrbit_succ, ← Q.sizes i (by omega)]
      exact Nat.floor_le (by positivity)
    · rw [Q.index_sizes (i+1), floorOrbit_succ, ← Q.index_sizes i]
      exact Nat.floor_le (by positivity)
  · rw [Q.extendedVertices_empty (by omega : Q.length < i+1),
      Q.extendedIndices_empty (by omega : Q.length < i+1)]
    simp only [Finset.card_empty, Nat.cast_zero]
    constructor <;> positivity

theorem Vortex.protected_size_bounds
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε ρ₀ ξ : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0 < Fintype.card V)
    (hD : (Fintype.card V : ℝ)/2 ≤ D)
    (hr : 0 < ρ₀) (hr1 : ρ₀ ≤ 1)
    (hrlo : ρ₀ ≤ initialIndexDensity U D) (hrhi : initialIndexDensity U D ≤ 1)
    (hb : 0 ≤ β) (hb1 : β ≤ 1/4) (he : 0 < ε) (he1 : ε ≤ 1/4)
    (hx : ε ≤ ξ/4) (hm : 0 < m) {i : ℕ} (hi : i < Q.length) :
    let P := Q.vertices i
    let H := Q.indices i
    let I := Q.vertices (i+1)
    let J := Q.indices (i+1)
    let T := Q.extendedVertices (i+2)
    let Z := Q.extendedIndices (i+2);
    T ⊆ I ∧ Z ⊆ J ∧ I ⊆ P ∧ J ⊆ H ∧
    ε/2 * P.card ≤ (I.card : ℝ) ∧ (I.card : ℝ) ≤ ε * P.card ∧
    ρ₀/8 * I.card ≤ (J.card : ℝ) ∧ 2*J.card ≤ I.card ∧
    (T.card : ℝ) ≤ ε*I.card ∧ (Z.card : ℝ) ≤ ε*J.card ∧
    (T.card : ℝ) ≤ ε^2*P.card ∧ (Z.card : ℝ) ≤ ε^2*P.card ∧
    (P.card : ℝ)/2 ≤ (P\T).card ∧
    ((P\T).card : ℝ)+(H\Z).card ≤ 2*P.card ∧
    ε/4*P.card ≤ ((I\T).card : ℝ) ∧
    ρ₀*ε/32*P.card ≤ ((J\Z).card : ℝ) ∧
    (ρ₀*ε/64)*((P\T).card+(H\Z).card : ℝ) ≤ ((I\T).card : ℝ) ∧
    (ρ₀*ε/64)*((P\T).card+(H\Z).card : ℝ) ≤ ((J\Z).card : ℝ) ∧
    ((I\T).card : ℝ)+(J\Z).card ≤ ξ*(P\T).card := by
  intro P H I J T Z
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hDp : 0 < D := by exact_mod_cast (show (0 : ℝ) < D by linarith only [hn',hD])
  have hTI : T ⊆ I := by
    change Q.extendedVertices (i+2) ⊆ Q.vertices (i+1)
    rw [← Q.extendedVertices_eq (by omega : i+1 ≤ Q.length)]
    exact Q.extendedVertices_subset (by omega)
  have hZJ : Z ⊆ J := by
    change Q.extendedIndices (i+2) ⊆ Q.indices (i+1)
    rw [← Q.extendedIndices_eq (by omega : i+1 ≤ Q.length)]
    exact Q.extendedIndices_subset (by omega)
  have hIP : I ⊆ P := Q.nested i hi
  have hJH : J ⊆ H := Q.indices_nested i
  obtain ⟨hIl,hIu⟩ := Q.consecutive_size_bounds he hm hi
  change ε*(P.card : ℝ)/2 ≤ I.card at hIl
  change (I.card : ℝ) ≤ ε*P.card at hIu
  have hJl := Q.index_size_lower hreg hn hD hr hrlo hb hb1 (by omega : i+1 ≤ Q.length)
  change ρ₀/8*(I.card : ℝ) ≤ J.card at hJl
  have hJu : 2*J.card ≤ I.card := Q.index_size_upper hreg hn hDp he.le hrhi (by omega)
  have hHu : 2*H.card ≤ P.card := Q.index_size_upper hreg hn hDp he.le hrhi hi.le
  obtain ⟨hTu,hZu⟩ := Q.extended_successor_size_bounds he.le (i+1)
  rw [Q.extendedVertices_eq (by omega : i+1 ≤ Q.length)] at hTu
  rw [Q.extendedIndices_eq (by omega : i+1 ≤ Q.length)] at hZu
  change (T.card : ℝ) ≤ ε*I.card at hTu
  change (Z.card : ℝ) ≤ ε*J.card at hZu
  have hJI : (J.card : ℝ) ≤ I.card := by exact_mod_cast (show J.card ≤ I.card by omega)
  have hHP : (H.card : ℝ) ≤ P.card := by exact_mod_cast (show H.card ≤ P.card by omega)
  have hI0 : (0 : ℝ) ≤ I.card := Nat.cast_nonneg _
  have hP0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hJ0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  have hTIu := mul_le_mul_of_nonneg_left hIu he.le
  have hZIu := mul_le_mul_of_nonneg_left hJI he.le
  have hT2 : (T.card : ℝ) ≤ ε^2*P.card := by nlinarith only [hTu,hTIu]
  have hZ2 : (Z.card : ℝ) ≤ ε^2*P.card := by nlinarith only [hZu,hZIu,hTIu]
  have heI := mul_le_mul_of_nonneg_right he1 hI0
  have heJ := mul_le_mul_of_nonneg_right he1 hJ0
  have hIPc : (I.card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card hIP
  have hTP : (T.card : ℝ) ≤ (P.card : ℝ)/2 := by linarith only [hTu,heI,hIPc]
  have hPc : ((P\T).card : ℝ) = (P.card : ℝ)-T.card := real_card_sdiff (hTI.trans hIP)
  have hIc : ((I\T).card : ℝ) = (I.card : ℝ)-T.card := real_card_sdiff hTI
  have hJc : ((J\Z).card : ℝ) = (J.card : ℝ)-Z.card := real_card_sdiff hZJ
  have hPa : (P.card : ℝ)/2 ≤ (P\T).card := by linarith only [hPc,hTP]
  have hpa : ((P\T).card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hha : ((H\Z).card : ℝ) ≤ H.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hamb : ((P\T).card : ℝ)+(H\Z).card ≤ 2*P.card := by linarith only [hpa,hha,hHP]
  have hIa : ε/4*P.card ≤ ((I\T).card : ℝ) := by linarith only [hIc,hTu,heI,hIl]
  have hjscaled := mul_le_mul_of_nonneg_left hIl (show 0 ≤ ρ₀/8 by positivity)
  have hJa : ρ₀*ε/32*P.card ≤ ((J\Z).card : ℝ) := by
    nlinarith only [hJc,hZu,heJ,hJl,hjscaled]
  have hscale := mul_le_mul_of_nonneg_left hamb (show 0 ≤ ρ₀*ε/64 by positivity)
  have hrscaled := mul_le_mul_of_nonneg_right hr1 (show 0 ≤ ε*(P.card : ℝ) by positivity)
  have hactiveI : ρ₀*ε/64*((P\T).card+(H\Z).card : ℝ) ≤ ((I\T).card : ℝ) := by
    nlinarith only [hscale,hrscaled,hIa,he.le,hP0]
  have hactiveJ : ρ₀*ε/64*((P\T).card+(H\Z).card : ℝ) ≤ ((J\Z).card : ℝ) := by
    nlinarith only [hscale,hJa]
  have hξ : 0 ≤ ξ := by linarith only [hx,he]
  have hxP := mul_le_mul_of_nonneg_right hx hP0
  have hxA := mul_le_mul_of_nonneg_left hPa hξ
  have hIaU : ((I\T).card : ℝ) ≤ I.card := by exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hJaU : ((J\Z).card : ℝ) ≤ I.card := by
    exact (show ((J\Z).card : ℝ) ≤ J.card by exact_mod_cast Finset.card_le_card Finset.sdiff_subset).trans hJI
  refine ⟨hTI,hZJ,hIP,hJH,by linarith only [hIl],hIu,hJl,hJu,hTu,hZu,hT2,hZ2,hPa,hamb,hIa,hJa,hactiveI,hactiveJ,?_⟩
  nlinarith only [hIaU,hJaU,hIu,hxP,hxA]

end Oberwolfach
