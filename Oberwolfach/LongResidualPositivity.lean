module

public import Oberwolfach.LongCapacityIntervalAssembly
public import Oberwolfach.ResidualPathPositivity

@[expose] public section

/-! Positivity needed for the pointwise cancellation follows from the original
transition product and the proved reserve bound, even when an input transport
matrix has zero entries. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_system_positive {X : Type*} [Fintype X]
    (a : ℕ → X → X → ℝ) (d : ℕ → X → ℝ)
    (ha : ∀ i x y, 0 ≤ a i x y) (hd : ∀ i x, 0 < d i x)
    (hrow : ∀ i x, ∑ y, a i x y=d i x)
    (hcol : ∀ i y, ∑ x, a i x y=d (i+1) y)
    (s L : Fin 3 → ℕ) (hL : ∀ i, 0 < L i)
    (hbd : ∀ i x, d (s i+L i) x=d (s (finRotate 3 i)) x)
    (hT : ∀ i x z, 0 < transitionWalk (capacityTransition a d) (s i) (L i) x z)
    (hres : ∀ (Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3))
      i j x y, pathEdgeLoad (longCapacityReserve a d s L Q i) j x y ≤ (11/27)*a (s i+j.val) x y) :
    ∀ Q i x z, 0 < threeIntervalResidualSystem (intervalCapacities a s L) (intervalDegrees d s L)
      (longCapacityReserve a d s L) Q i x z := by
  let R := capacityTransition a d
  let A := intervalCapacities a s L
  let D := intervalDegrees d s L
  let ρ := longCapacityReserve a d s L
  have hR := capacityTransition_isTransition a d ha hd hrow
  have hD (i : Fin 3) (j : Fin (L i+1)) (x : X) : 0 < D i j x := hd _ _
  have hA (i : Fin 3) (j : Fin (L i)) (x y : X) : 0 ≤ A i j x y := ha _ _ _
  have hAr (i : Fin 3) (j : Fin (L i)) (x : X) : (∑ y, A i j x y)=D i j.castSucc x := hrow _ _
  have hAc (i : Fin 3) (j : Fin (L i)) (y : X) : (∑ x, A i j x y)=D i j.succ y := by
    simpa only [A,D,intervalCapacities,intervalDegrees,Fin.val_succ,Nat.add_assoc] using hcol (s i+j.val) y
  intro Q i x z
  have hQ : Q.val i ∈ transportMatrices (fun x => D i 0 x/3) (fun z => D i (Fin.last (L i)) z/3) := by
    have hh := Q.property i (Set.mem_univ i)
    change Q.val i ∈ transportMatrices (fun x => d (s i) x/3) (fun z => d (s (finRotate 3 i)) z/3) at hh
    simpa only [D,intervalDegrees,Fin.val_zero,Nat.add_zero,Fin.val_last,hbd] using hh
  have hρ0 (p : Fin (L i+1) → X) : 0 ≤ ρ Q i p :=
    reservedPathWeight_nonneg R hR (s i) (L i) (Q.val i) hQ.1 p
  have hρend (x z : X) : (∑ p, if p 0=x ∧ p (Fin.last (L i))=z then ρ Q i p else 0)=Q.val i x z :=
    reservedPathWeight_endpoints R (s i) (L i) (Q.val i) (hT i) x z
  have hpkg := halfResidualPathWeight_properties (hL i) (A i) (D i) (ρ Q i) (Q.val i)
    (hA i) (hD i) (hAr i) (hAc i) hρ0 (hres Q i) hρend hQ
  obtain ⟨p,hpx,hpz,hpath⟩ := positive_transition_path_exists R hR (s i) (L i) x z (hT i x z)
  have haPath (j : Fin (L i)) : 0 < A i j (p j.castSucc) (p j.succ) := by
    have hh := hpath j
    change 0 < a (s i+j.val) (p j.castSucc) (p j.succ) / d (s i+j.val) (p j.castSucc) at hh
    exact (div_pos_iff_of_pos_right (hd _ _)).mp hh
  have hpos := halfResidualPathWeight_pos (hL i) (A i) (D i) (ρ Q i)
    (hA i) (hD i) (hAr i) (hAc i) hρ0 (hres Q i) p haPath
  exact pathEndpointMatrix_pos_of_path _ hpkg.1 x z p ⟨hpx,hpz⟩ hpos

end Oberwolfach
