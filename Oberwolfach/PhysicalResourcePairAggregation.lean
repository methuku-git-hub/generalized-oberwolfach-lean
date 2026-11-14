module

public import Oberwolfach.TypedMarkedLoadBounds
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section
/-! Transfer weighted pair bounds through a many-to-one physical-resource
map. A physical pair is counted at most once on the left; the right side
sums all typed preimages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A B C:Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B]

theorem physical_resource_pair_weight_le_fibers
    (φ:A→B) (R:C→Finset A) (w:C→ℝ) (hw:∀c,0≤w c) (x y:B) (hxy:x≠y):
    (∑c,if x∈(R c).image φ ∧ y∈(R c).image φ then w c else 0) ≤
      ∑a∈Finset.univ.filter (fun a=>φ a=x),∑b∈Finset.univ.filter (fun b=>φ b=y),
        resourceOmittedPairWeight R w a b := by
  let X:=Finset.univ.filter (fun a=>φ a=x)
  let Y:=Finset.univ.filter (fun b=>φ b=y)
  have hterm (c:C):
      (if x∈(R c).image φ ∧ y∈(R c).image φ then w c else 0) ≤
      ∑a∈X,∑b∈Y,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0 := by
    by_cases h:x∈(R c).image φ ∧ y∈(R c).image φ
    · obtain ⟨a,ha,hax⟩:=Finset.mem_image.mp h.1
      obtain ⟨b,hb,hby⟩:=Finset.mem_image.mp h.2
      have hab:a≠b:=by intro e;apply hxy;rw [←hax,←hby,e]
      have haX:a∈X:=by simp [X,hax]
      have hbY:b∈Y:=by simp [Y,hby]
      have hinner:(w c)≤∑b∈Y,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0 := by
        have hh:=Finset.single_le_sum (s:=Y) (f:=fun b=>if a∈R c ∧ b∈R c ∧ a≠b then w c else 0)
          (fun b _=>by split_ifs <;> simp_all) hbY
        simpa [ha,hb,hab] using hh
      have houter: (∑b∈Y,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0) ≤
          ∑a∈X,∑b∈Y,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0 := by
        apply Finset.single_le_sum _ haX
        intro a _
        apply Finset.sum_nonneg
        intro b _
        split_ifs <;> simp_all
      simpa [h] using hinner.trans houter
    · simp only [h,ite_false]
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro b _
      split_ifs <;> simp_all
  calc
    _ ≤ ∑c,∑a∈X,∑b∈Y,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0 := Finset.sum_le_sum (fun c _=>hterm c)
    _ = ∑a∈X,∑b∈Y,∑c,if a∈R c ∧ b∈R c ∧ a≠b then w c else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold resourceOmittedPairWeight
      apply Finset.sum_congr rfl
      intro c _
      by_cases h:a≠b
      · simp [h,Ne.symm h]
      · have he:a=b:=not_ne_iff.mp h
        subst b
        simp

end Oberwolfach
