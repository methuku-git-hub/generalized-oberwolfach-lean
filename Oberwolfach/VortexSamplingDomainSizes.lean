module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section

/-! The actual fixed vortex domains satisfy the finite-family and geometric
summability conditions used by the common-event sampling estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nested_contracting_difference_sizes {X : Type*} [DecidableEq X]
    (A : ℕ→Finset X) (ε : ℝ) (he : 0≤ε) (he1 : ε≤1/4)
    (hnest : ∀ i j,i≤ j→A j⊆A i)
    (hstep : ∀ i,((A (i+1)).card:ℝ)≤ε*(A i).card)
    (i d : ℕ) (hd : 1≤ d) :
    (3/4:ℝ)*(A i).card≤(A i\A (i+d)).card ∧
    ((A i\A (i+d)).card:ℝ)≤(A i).card ∧
    ((A (i+1)\A (i+1+d)).card:ℝ)≤(2*ε)*(A i\A (i+d)).card := by
  have hlate : ((A (i+d)).card:ℝ)≤(A (i+1)).card := by
    exact_mod_cast Finset.card_le_card (hnest (i+1) (i+d) (by omega))
  have hu := hstep i
  have hec := mul_le_mul_of_nonneg_right he1 (Nat.cast_nonneg (A i).card)
  have hc := real_card_sdiff (hnest i (i+d) (by omega))
  have hlo : (3/4:ℝ)*(A i).card≤(A i\A (i+d)).card := by
    linarith only [hc,hlate,hu,hec]
  have hu' : ((A (i+1)\A (i+1+d)).card:ℝ)≤(A (i+1)).card := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A (i+1)\A (i+1+d)⊆A (i+1))
  have hp := mul_le_mul_of_nonneg_left hlo he
  have hnonneg : (0:ℝ)≤ε*(A i).card := mul_nonneg he (Nat.cast_nonneg _)
  refine ⟨hlo,?_,?_⟩
  · exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : A i\A (i+d)⊆A i)
  · nlinarith only [hp,hu',hu,hnonneg]

theorem Vortex.number_of_levels_le_order
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0<ε) (he1 : ε<1) (hm : 0< m) : Q.length+1≤ Fintype.card V := by
  have hp (i : ℕ) (hi : i≤ Q.length) : 0<(Q.vertices i).card := by
    have hh := Q.vertices_lower hi
    have hm' : (0:ℝ)< m := by exact_mod_cast hm
    exact_mod_cast (show (0:ℝ)<(Q.vertices i).card by nlinarith only [hh,mul_pos he hm'])
  have hdec (i : ℕ) (hi : i< Q.length) : (Q.vertices (i+1)).card<(Q.vertices i).card := by
    have hn : (0:ℝ)<(Q.vertices i).card := by exact_mod_cast hp i hi.le
    have hs := (Q.consecutive_size_bounds he hm hi).2
    have hm := mul_lt_mul_of_pos_right he1 hn
    exact_mod_cast (show ((Q.vertices (i+1)).card:ℝ)<(Q.vertices i).card by linarith only [hs,hm])
  have hbound : ∀ i,i≤ Q.length→i+(Q.vertices i).card≤ Fintype.card V := by
    intro i
    induction i with
    | zero=>intro hi;rw [Q.sizes 0 hi];simp [floorOrbit_zero]
    | succ i ih=>intro hi;have hh:=ih (by omega);have hd:=hdec i (by omega);omega
  have hh:=hbound Q.length le_rfl
  have hpos:=hp Q.length le_rfl
  omega

theorem Vortex.sampling_difference_sizes
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε ρ₀ : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0< Fintype.card V)
    (hD : (Fintype.card V:ℝ)/2≤ D) (hr : 0<ρ₀)
    (hrlo : ρ₀≤ initialIndexDensity U D) (hb : 0≤β) (hb1 : β≤1/4)
    (he : 0<ε) (he1 : ε≤1/4) (i d : ℕ) (hd : 1≤ d) (hi : i≤ Q.length) :
    let A := Q.extendedVertices i\Q.extendedVertices (i+d)
    let B := Q.extendedIndices i\Q.extendedIndices (i+d);
    3*ε*m/8≤(A.card:ℝ) ∧
    3*ρ₀*ε*m/64≤(B.card:ℝ) ∧
    ((Q.extendedVertices (i+1)\Q.extendedVertices (i+1+d)).card:ℝ)≤(2*ε)*A.card ∧
    ((Q.extendedIndices (i+1)\Q.extendedIndices (i+1+d)).card:ℝ)≤(2*ε)*B.card ∧
    ((Q.vertices i).card:ℝ)≤(4/3)*A.card ∧
    ((Q.indices i).card:ℝ)≤(4/3)*B.card := by
  intro A B
  have hv := nested_contracting_difference_sizes Q.extendedVertices ε he.le he1
    (fun i j h=>Q.extendedVertices_subset h) (fun i=>(Q.extended_successor_size_bounds he.le i).1) i d hd
  have hu := nested_contracting_difference_sizes Q.extendedIndices ε he.le he1
    (fun i j h=>Q.extendedIndices_subset h) (fun i=>(Q.extended_successor_size_bounds he.le i).2) i d hd
  change (3/4:ℝ)*(Q.extendedVertices i).card≤ A.card ∧ _ ∧ _ at hv
  change (3/4:ℝ)*(Q.extendedIndices i).card≤ B.card ∧ _ ∧ _ at hu
  have hvl := hv.1
  have hul := hu.1
  rw [Q.extendedVertices_eq hi] at hvl
  rw [Q.extendedIndices_eq hi] at hul
  have hl := Q.vertices_lower hi
  have hulow := Q.index_size_lower hreg hn hD hr hrlo hb hb1 hi
  have hscale := mul_le_mul_of_nonneg_left hl (show 0≤ρ₀/8 by positivity)
  refine ⟨?_,?_,hv.2.2,hu.2.2,?_,?_⟩
  · nlinarith only [hvl,hl]
  · nlinarith only [hul,hulow,hscale]
  · linarith only [hvl]
  · linarith only [hul]

end Oberwolfach
