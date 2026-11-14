module

public import Oberwolfach.BalancedCapacityTransitions
public import Oberwolfach.ThreeIntervalCapacityAssembly

@[expose] public section

/-! Instantiation of the three-interval fixed-point construction by locally
balanced capacities and the proved long-path reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def intervalCapacities {X : Type*} (a : ℕ → X → X → ℝ) (s L : Fin 3 → ℕ)
    (i : Fin 3) (j : Fin (L i)) : X → X → ℝ := a (s i+j.val)

def intervalDegrees {X : Type*} (d : ℕ → X → ℝ) (s L : Fin 3 → ℕ)
    (i : Fin 3) (j : Fin (L i+1)) : X → ℝ := d (s i+j.val)

def longCapacityReserve {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ) (s L : Fin 3 → ℕ)
    (Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3))
    (i : Fin 3) : (Fin (L i+1) → X) → ℝ :=
  reservedPathWeight (capacityTransition a d) (s i) (L i) (Q.val i)

set_option maxHeartbeats 800000 in
theorem long_capacity_interval_assembly {X : Type*} [Fintype X]
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
      ∀ x y, κ*capacityProfile d M (j+3) y ≤ transitionWalk (capacityTransition a d) j 3 x y) :
    ∃ Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3),
    ∃ ω : (∀ i, Fin (L i+1) → X) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p)=M ∧
      (∀ (i : Fin 3) (j : Fin (L i)) (x y : X), (∑ p, if p i j.castSucc=x ∧ p i j.succ=y then ω p else 0)=a (s i+j.val) x y) ∧
      (∀ p, 0 < ω p → ∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0) ∧
      (∀ i x z, Q.val i x z=walkTransport (threeIntervalMarginal (intervalDegrees d s L))
        (threeIntervalResidualSystem (intervalCapacities a s L) (intervalDegrees d s L)
          (longCapacityReserve a d s L) Q) (finRotate 3) (finRotate 3 i) 2 z x) ∧
      (∀ p, (∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0) →
        ω p=∑ c, threeIntervalSector (intervalCapacities a s L) (intervalDegrees d s L)
          (longCapacityReserve a d s L) Q c p) := by
  let R := capacityTransition a d
  let π := capacityProfile d M
  have hR := capacityTransition_isTransition a d ha hd hrow
  obtain ⟨hπpos,hπsum⟩ := capacityProfile_distribution d M hM hd hms
  have hπ := capacityProfile_stationary a d M hd hcol
  have hMp (j : ℕ) (x : X) : M*π j x=d j x := by
    change M*(d j x/M)=d j x
    field_simp [hM.ne']
  have hmix (i : Fin 3) := long_interval_mixing R π hR (fun j x => (hπpos j x).le)
    hπsum hπ J hJ κ B hκ hκ1 hB (s i) (L i) t (hupper i) (hminor i) ht (by have := hL i; omega)
  have hT (i : Fin 3) (x z : X) : 0 < transitionWalk R (s i) (L i) x z := by
    have hh := (abs_le.mp (hmix i x z)).1
    have hp := hπpos (s i+L i) z
    change 0 < π (s i+L i) z at hp
    linarith
  let A := intervalCapacities a s L
  let D := intervalDegrees d s L
  let ρ := longCapacityReserve a d s L
  have hD (i : Fin 3) (j : Fin (L i+1)) (x : X) : 0 < D i j x := hd _ _
  have hArow (i : Fin 3) (j : Fin (L i)) (x : X) : (∑ y, A i j x y)=D i j.castSucc x := hrow _ _
  have hAcol (i : Fin 3) (j : Fin (L i)) (y : X) : (∑ x, A i j x y)=D i j.succ y := by
    simpa only [A,D,intervalCapacities,intervalDegrees,Fin.val_succ,Nat.add_assoc] using hcol (s i+j.val) y
  have hDb (i : Fin 3) (x : X) : D i (Fin.last (L i)) x=D (finRotate 3 i) 0 x := by
    simpa only [D,intervalDegrees,Fin.val_last,Fin.val_zero,Nat.add_zero] using hbd i x
  have hDm (i : Fin 3) : (∑ x, D i 0 x)=M := by
    simpa only [D,intervalDegrees,Fin.val_zero,Nat.add_zero] using hms (s i)
  have hρcont (i : Fin 3) (p : Fin (L i+1) → X) : Continuous (fun Q => ρ Q i p) := by
    change Continuous (fun Q : transportProduct (threeIntervalMarginal D) (finRotate 3) =>
      reservedPathWeight R (s i) (L i) (Q.val i) p)
    exact reservedPathWeight_continuous R (s i) (L i)
      (fun Q : transportProduct (threeIntervalMarginal D) (finRotate 3) => Q.val i)
      (by
        intro x z
        exact (continuous_apply z).comp ((continuous_apply x).comp
          ((continuous_apply i).comp continuous_subtype_val))) p
  have hρ0 (Q : transportProduct (threeIntervalMarginal D) (finRotate 3)) (i : Fin 3) (p : Fin (L i+1) → X) :
      0 ≤ ρ Q i p := reservedPathWeight_nonneg R hR (s i) (L i) (Q.val i) (Q.property i (Set.mem_univ i)).1 p
  have hρend (Q : transportProduct (threeIntervalMarginal D) (finRotate 3)) (i : Fin 3) :
      pathEndpointMatrix (ρ Q i)=Q.val i := by
    funext x z
    exact reservedPathWeight_endpoints R (s i) (L i) (Q.val i) (hT i) x z
  have hρedge (Q : transportProduct (threeIntervalMarginal D) (finRotate 3)) (i : Fin 3)
      (j : Fin (L i)) (x y : X) : pathEdgeLoad (ρ Q i) j x y ≤ (11/27)*A i j x y := by
    have hQ : Q.val i ∈ transportMatrices (fun x => M*π (s i) x/3) (fun z => M*π (s i+L i) z/3) := by
      simp only [hMp,hbd]
      exact Q.property i (Set.mem_univ i)
    have hh := long_reserved_path_edge_bound R π hR hπpos hπsum hπ J hJ κ B M hκ hκ1 hB
      (s i) (L i) t ht (hL i) (hupper i) (hminor i) (Q.val i) hQ j x y
    rw [capacityTransition_reconstruct a d M hM.ne' (fun i x => (hd i x).ne')] at hh
    exact hh
  exact three_interval_capacity_assembly L (fun i => by have := hL i; omega) A D M hM
    (fun _ _ _ _ => ha _ _ _) hD hArow hAcol hDb hDm ρ hρcont hρ0 hρend hρedge

end Oberwolfach
