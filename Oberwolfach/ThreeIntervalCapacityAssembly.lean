module

public import Oberwolfach.ResidualPathEndpoints
public import Oberwolfach.FractionalCycleAssembly
public import Oberwolfach.IntervalPathWeights

@[expose] public section

/-! Three finite capacity intervals synchronized by the proved fixed-point
construction. The local reserve hypotheses are discharged for long intervals
by the explicit transition-path construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def threeIntervalMarginal {X : Type*} {L : Fin 3 → ℕ}
    (d : ∀ i, Fin (L i+1) → X → ℝ) (i : Fin 3) (x : X) : ℝ := d i 0 x/3

def threeIntervalResidualSystem {X : Type*} [Fintype X] {L : Fin 3 → ℕ}
    (a : ∀ i, Fin (L i) → X → X → ℝ) (d : ∀ i, Fin (L i+1) → X → ℝ)
    (ρ : transportProduct (threeIntervalMarginal d) (finRotate 3) → ∀ i, (Fin (L i+1) → X) → ℝ)
    (Q : transportProduct (threeIntervalMarginal d) (finRotate 3)) (i : Fin 3) : X → X → ℝ :=
  pathEndpointMatrix (halfResidualPathWeight (a i) (d i) (ρ Q i))

def threeIntervalSector {X : Type*} [Fintype X] {L : Fin 3 → ℕ}
    (a : ∀ i, Fin (L i) → X → X → ℝ) (d : ∀ i, Fin (L i+1) → X → ℝ)
    (ρ : transportProduct (threeIntervalMarginal d) (finRotate 3) → ∀ i, (Fin (L i+1) → X) → ℝ)
    (Q : transportProduct (threeIntervalMarginal d) (finRotate 3)) (c : Fin 3)
    (p : ∀ i, Fin (L i+1) → X) : ℝ :=
  chainJoint (threeIntervalMarginal d) (threeIntervalResidualSystem a d ρ Q) (finRotate 3)
    (finRotate 3 c) 2 (fun j => p (cyclicChainOrder c j) 0) *
    ∏ i, (if i=c then ρ Q i (p i) else halfResidualPathWeight (a i) (d i) (ρ Q i) (p i)) /
      (if i=c then Q.val c (p i 0) (p i (Fin.last (L i)))
        else threeIntervalResidualSystem a d ρ Q i (p i 0) (p i (Fin.last (L i))))

set_option maxHeartbeats 800000 in
theorem three_interval_capacity_assembly {X : Type*} [Fintype X]
    (L : Fin 3 → ℕ) (hL : ∀ i, 0 < L i)
    (a : ∀ i, Fin (L i) → X → X → ℝ) (d : ∀ i, Fin (L i+1) → X → ℝ)
    (M : ℝ) (hM : 0 < M)
    (ha : ∀ i j x y, 0 ≤ a i j x y) (hd : ∀ i j x, 0 < d i j x)
    (hrow : ∀ i j x, ∑ y, a i j x y=d i j.castSucc x)
    (hcol : ∀ i j y, ∑ x, a i j x y=d i j.succ y)
    (hbd : ∀ i x, d i (Fin.last (L i)) x=d (finRotate 3 i) 0 x)
    (hms : ∀ i, ∑ x, d i 0 x=M)
    (ρ : transportProduct (threeIntervalMarginal d) (finRotate 3) → ∀ i, (Fin (L i+1) → X) → ℝ)
    (hρcont : ∀ i p, Continuous (fun Q => ρ Q i p))
    (hρ0 : ∀ Q i p, 0 ≤ ρ Q i p)
    (hρend : ∀ Q i, pathEndpointMatrix (ρ Q i)=Q.val i)
    (hρedge : ∀ Q i j x y, pathEdgeLoad (ρ Q i) j x y ≤ (11/27)*a i j x y) :
    ∃ Q : transportProduct (threeIntervalMarginal d) (finRotate 3),
    ∃ ω : (∀ i, Fin (L i+1) → X) → ℝ,
      (∀ p, 0 ≤ ω p) ∧ (∑ p, ω p)=M ∧
      (∀ i j x y, (∑ p, if p i j.castSucc=x ∧ p i j.succ=y then ω p else 0)=a i j x y) ∧
      (∀ p, 0 < ω p → ∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0) ∧
      (∀ i x z, Q.val i x z=walkTransport (threeIntervalMarginal d)
        (threeIntervalResidualSystem a d ρ Q) (finRotate 3) (finRotate 3 i) 2 z x) ∧
      (∀ p, (∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0) →
        ω p=∑ c, threeIntervalSector a d ρ Q c p) := by
  let m := threeIntervalMarginal d
  let S (Q : transportProduct m (finRotate 3)) (i : Fin 3) := halfResidualPathWeight (a i) (d i) (ρ Q i)
  let H := threeIntervalResidualSystem a d ρ
  have hQmat (Q : transportProduct m (finRotate 3)) (i : Fin 3) : Q.val i ∈
      transportMatrices (fun x => d i 0 x/3) (fun z => d i (Fin.last (L i)) z/3) := by
    have hh := Q.property i (Set.mem_univ i)
    change Q.val i ∈ transportMatrices (fun x => d i 0 x/3)
      (fun z => d (finRotate 3 i) 0 z/3) at hh
    simpa only [hbd] using hh
  have hprop (Q : transportProduct m (finRotate 3)) (i : Fin 3) :=
    halfResidualPathWeight_properties (hL i) (a i) (d i) (ρ Q i) (Q.val i) (ha i) (hd i)
      (hrow i) (hcol i) (hρ0 Q i) (hρedge Q i)
      (fun x z => congrFun (congrFun (hρend Q i) x) z) (hQmat Q i)
  have hHm (Q : transportProduct m (finRotate 3)) (i : Fin 3) :
      H Q i ∈ transportMatrices (m i) (m (finRotate 3 i)) := by
    change pathEndpointMatrix (halfResidualPathWeight (a i) (d i) (ρ Q i)) ∈
      transportMatrices (fun x => d i 0 x/3) (fun z => d (finRotate 3 i) 0 z/3)
    simpa only [hbd] using
      halfResidualEndpoint_mem (hL i) (a i) (d i) (ρ Q i) (Q.val i) (ha i) (hd i)
        (hrow i) (hcol i) (hρ0 Q i) (hρedge Q i) (hρend Q i) (hQmat Q i)
  have hScont (i : Fin 3) : Continuous (fun Q => S Q i) := by
    apply halfResidualPathWeight_continuous _ _ _ (hρcont i)
    intro Q j x
    exact (half_pos (hd i j x)).trans_le
      ((residualIntervalDegree_bounds (hL i) (a i) (d i) (ρ Q i) (hρ0 Q i) (hd i)
        (hrow i) (hcol i) (hρedge Q i) j x).1)
  have hHcont : Continuous H := by
    apply continuous_pi
    intro i
    exact pathEndpointMatrix_continuous (fun Q => S Q i)
      (fun p => (continuous_apply p).comp (hScont i))
  have hm (i : Fin 3) (x : X) : 0 < m i x := div_pos (hd i 0 x) (by norm_num)
  have hmt (i : Fin 3) : (∑ x, m i x)=M/3 := by
    change (∑ x, d i 0 x/3)=M/3
    rw [← Finset.sum_div,hms]
  have hρsum (Q : transportProduct m (finRotate 3)) (i : Fin 3) : (∑ p, ρ Q i p)=M/3 := by
    rw [← pathVertexLoad_total (ρ Q i) 0]
    have hh := pathVertexLoad_endpoints (ρ Q i) (Q.val i)
      (fun x z => congrFun (congrFun (hρend Q i) x) z)
    simp_rw [hh.1,(hQmat Q i).2.1]
    rw [← Finset.sum_div,hms]
  have hSsum (Q : transportProduct m (finRotate 3)) (i : Fin 3) : (∑ p, S Q i p)=M/3 := by
    rw [← pathVertexLoad_total (S Q i) 0]
    change (∑ x, pathVertexLoad (halfResidualPathWeight (a i) (d i) (ρ Q i)) 0 x)=M/3
    simp_rw [(hprop Q i).2.2.1]
    rw [← Finset.sum_div,hms]
  obtain ⟨Q,ω,hω,ht,hmarg,hclosed,hfixed,hformula⟩ := fractional_cycle_path_assembly_with_formula
    m (M/3) (div_pos hM (by norm_num)) hm hmt
    (fun i p => (p 0,p (Fin.last (L i)))) H hHcont hHm ρ S hρ0
    (fun Q i => (hprop Q i).1) hρsum hSsum
    (by
      intro Q i x z
      simpa only [Prod.mk.injEq,pathEndpointMatrix] using congrFun (congrFun (hρend Q i) x) z)
    (by intro Q i x z; simp only [Prod.mk.injEq]; rfl)
  refine ⟨Q,ω,hω,?_,?_,hclosed,hfixed,?_⟩
  · convert ht using 1 <;> norm_num <;> ring
  · intro i j x y
    have hh := finite_marginal_test ω (fun p => p i) (fun p => ρ Q i p+2*S Q i p)
      (by convert hmarg i using 1 <;> norm_num) (fun p => if p j.castSucc=x ∧ p j.succ=y then (1 : ℝ) else 0)
    simp only [mul_ite,mul_one,mul_zero] at hh
    rw [hh]
    have heq : (∑ p, if p j.castSucc=x ∧ p j.succ=y then ρ Q i p+2*S Q i p else 0)=
        pathEdgeLoad (ρ Q i) j x y+2*pathEdgeLoad (S Q i) j x y := by
      unfold pathEdgeLoad
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    rw [heq,(hprop Q i).2.1]
    ring
  · intro p hp
    exact hformula p hp

end Oberwolfach
