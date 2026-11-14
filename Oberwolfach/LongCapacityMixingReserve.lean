module

public import Oberwolfach.LongCapacityIntervalAssembly

@[expose] public section

/-! Mixing and reserve estimates used by both exact assembly and pointwise bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_capacity_mixing_reserve {X : Type*} [Fintype X]
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
    (∀ i x z, |transitionWalk (capacityTransition a d) (s i) (L i) x z-
      capacityProfile d M (s i+L i) z| ≤ (1/10)*capacityProfile d M (s i+L i) z) ∧
    (∀ (Q : transportProduct (threeIntervalMarginal (intervalDegrees d s L)) (finRotate 3))
      i j x y, pathEdgeLoad (longCapacityReserve a d s L Q i) j x y ≤ (11/27)*a (s i+j.val) x y) := by
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
  refine ⟨hmix,?_⟩
  intro Q i j x y
  have hQ : Q.val i ∈ transportMatrices (fun x => M*π (s i) x/3) (fun z => M*π (s i+L i) z/3) := by
    simp only [hMp,hbd]
    exact Q.property i (Set.mem_univ i)
  have hh := long_reserved_path_edge_bound R π hR hπpos hπsum hπ J hJ κ B M hκ hκ1 hB
    (s i) (L i) t ht (hL i) (hupper i) (hminor i) (Q.val i) hQ j x y
  rw [capacityTransition_reconstruct a d M hM.ne' (fun i x => (hd i x).ne')] at hh
  exact hh

end Oberwolfach
