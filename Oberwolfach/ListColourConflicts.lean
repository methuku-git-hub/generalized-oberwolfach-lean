module

public import Oberwolfach.EqualizedColourRetention
public import Oberwolfach.CoordinateLocalLemmaDegree

@[expose] public section

/-! The events that two adjacent vertices choose the same specified
colour. Their coordinate incidence is bounded by the colour degrees, not
by the total number of vertices or the total number of colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def listColourConflicts {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) : Finset (V×V×C) :=
  Finset.univ.filter (fun p=>G.Adj p.1 p.2.1 ∧ p.2.2∈L p.1 ∧ p.2.2∈L p.2.1)

abbrev ListColourConflict {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) := {p // p∈listColourConflicts G L}

def listColourConflictSupport {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (p : ListColourConflict G L) : Finset V :=
  {p.val.1,p.val.2.1}

theorem listColourConflictSupport_size {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (p : ListColourConflict G L) :
    (listColourConflictSupport G L p).card≤2 := by
  classical
  apply (Finset.card_insert_le _ _).trans
  simp

theorem listColourConflictSupport_incidence
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) {l d : ℕ}
    (hcard : ∀ v,(L v).card=l)
    (hdegree : ∀ v c,(colourNeighbourSet G L v c).card≤d) (v : V) :
    (Finset.univ.filter (fun p : ListColourConflict G L=>v∈listColourConflictSupport G L p)).card≤2*l*d := by
  classical
  let A := (L v).biUnion (fun c=>(colourNeighbourSet G L v c).image (fun w=>(v,w,c)))
  let B := (L v).biUnion (fun c=>(colourNeighbourSet G L v c).image (fun w=>(w,v,c)))
  have hA : A.card≤l*d := by
    apply (Finset.card_biUnion_le_card_mul _ _ _ (fun c _=>
      Finset.card_image_le.trans (hdegree v c))).trans
    rw [hcard]
  have hB : B.card≤l*d := by
    apply (Finset.card_biUnion_le_card_mul _ _ _ (fun c _=>
      Finset.card_image_le.trans (hdegree v c))).trans
    rw [hcard]
  have hc : (Finset.univ.filter (fun p : ListColourConflict G L=>v∈listColourConflictSupport G L p)).card≤
      (A∪B).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro p hp
      have hv : v=p.val.1 ∨ v=p.val.2.1 := by
        simpa only [listColourConflictSupport,Finset.mem_insert,Finset.mem_singleton] using
          (Finset.mem_filter.mp hp).2
      have hcond : G.Adj p.val.1 p.val.2.1 ∧ p.val.2.2∈L p.val.1 ∧ p.val.2.2∈L p.val.2.1 := by
        simpa only [listColourConflicts,Finset.mem_filter,Finset.mem_univ,true_and] using p.property
      rcases hv with hv|hv
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨p.val.2.2,by simpa only [hv] using hcond.2.1,?_⟩
        apply Finset.mem_image.mpr
        refine ⟨p.val.2.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hv] using hcond.1,hcond.2.2⟩,?_⟩
        simp only [hv]
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨p.val.2.2,by simpa only [hv] using hcond.2.2,?_⟩
        apply Finset.mem_image.mpr
        refine ⟨p.val.1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hv] using hcond.1.symm,hcond.2.1⟩,?_⟩
        simp only [hv]
    · intro p hp q hq he
      exact Subtype.ext he
  calc
    _ ≤ A.card+B.card := hc.trans (Finset.card_union_le A B)
    _ ≤ l*d+l*d := add_le_add hA hB
    _ = _ := by ring

end Oberwolfach
