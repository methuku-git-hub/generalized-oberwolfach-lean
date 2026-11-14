module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.OrdinaryAdmissibleCycleLoads
public import Oberwolfach.OrdinaryCycleWeightRestriction
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! The ordinary local potential is defined on every ambient root. When
that root belongs to the spoke common neighbourhood, it is exactly the
vertex sum on the surviving cycle family. Parent coefficients are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}

def localOrdinaryParent {P Q F : SimpleGraph V} {T : Finset V} (hQP : Q≤P)
    (C : LocalOrdinaryCycle Q F T r) : OrdinaryCycle P r := ⟨C.val.val,C.val.property.trans hQP⟩

def localOrdinaryParentEquiv (P Q F : SimpleGraph V) (T : Finset V) (hQP : Q≤P) :
    LocalOrdinaryCycle Q F T r ≃ {C : OrdinaryCycle P r // C.val.val≤Q ∧
      (∀ v∈C.val.val.support,v∈T) ∧ ∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y} where
  toFun C := ⟨localOrdinaryParent hQP C,C.val.property,C.property⟩
  invFun C := ⟨⟨C.val.val,C.property.1⟩,C.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem localOrdinary_sum (P Q F : SimpleGraph V) (T : Finset V) (hQP : Q≤P)
    (f : OrdinaryCycle P r→ℝ) :
    (∑ C : LocalOrdinaryCycle Q F T r,f (localOrdinaryParent hQP C))=
      ∑ C : OrdinaryCycle P r,if C.val.val≤Q ∧ (∀ v∈C.val.val.support,v∈T) ∧
        (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then f C else 0 := by
  let good := fun C : OrdinaryCycle P r=>C.val.val≤Q ∧ (∀ v∈C.val.val.support,v∈T) ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y)
  have hh := finite_sum_restrict_of_zero good (fun C=>if good C then f C else 0) (fun C h=>if_neg h)
  have hs := (localOrdinaryParentEquiv (r:=r) P Q F T hQP).symm.sum_comp
    (fun C=>f (localOrdinaryParent hQP C))
  calc
    _ = ∑ C : {C : OrdinaryCycle P r // good C},f C.val := hs.symm
    _ = ∑ C : {C : OrdinaryCycle P r // good C},if good C.val then f C.val else 0 := by
      apply Finset.sum_congr rfl;intro C _;exact (if_pos C.property).symm
    _ = _ := by convert hh.symm using 1 <;> congr!

def ordinaryLocalPotential (P Q F : SimpleGraph V) (T : Finset V)
    (φ : OrdinaryCycle P r→ℝ) (v : V) : ℝ :=
  ∑ C,if v∈C.val.val.support ∧ C.val.val≤Q ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) ∧
    (∀ z∈C.val.val.support,z≠v → z∈T) then φ C else 0

def ordinaryLocalTarget (P F : SimpleGraph V) (weight : OrdinaryCycle P r→ℝ) (D : ℝ) (v : V) : ℝ :=
  (2/D)*∑ C,if v∈C.val.val.support ∧
    (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y) then weight C else 0

theorem ordinaryLocalPotential_present (P Q F : SimpleGraph V) (T : Finset V) (hQP : Q≤P)
    (φ : OrdinaryCycle P r→ℝ) (v : V) (hv : v∈T) :
    ordinaryLocalPotential P Q F T φ v=
      hypergraphWeightedDegree localOrdinaryVertices (fun C : LocalOrdinaryCycle Q F T r=>φ (localOrdinaryParent hQP C)) v := by
  have hh := localOrdinary_sum P Q F T hQP (fun C=>if v∈C.val.val.support then φ C else 0)
  unfold hypergraphWeightedDegree
  simp only [localOrdinaryVertices,Set.mem_toFinset]
  change ordinaryLocalPotential P Q F T φ v=∑ C : LocalOrdinaryCycle Q F T r,
    if v∈(localOrdinaryParent hQP C).val.val.support then φ (localOrdinaryParent hQP C) else 0
  rw [hh]
  unfold ordinaryLocalPotential
  apply Finset.sum_congr rfl
  intro C _
  have ht : (∀ z∈C.val.val.support,z≠v → z∈T)↔∀ z∈C.val.val.support,z∈T := by
    constructor
    · intro h z hz;by_cases he : z=v
      · exact he ▸ hv
      · exact h z hz he
    · intro h z hz _;exact h z hz
  simp only [ht]
  by_cases hroot : v∈C.val.val.support <;> by_cases hQ : C.val.val≤Q <;>
    by_cases hT : ∀ z∈C.val.val.support,z∈T <;>
    by_cases hF : ∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬F.Adj x y <;>
    simp only [hroot,hQ,hT,hF,and_true,true_and,and_false,false_and,ite_true,ite_false,ite_self] <;> simp only [and_comm]

end Oberwolfach
