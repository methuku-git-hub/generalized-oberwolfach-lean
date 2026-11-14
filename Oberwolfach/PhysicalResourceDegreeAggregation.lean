module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Aggregate typed resource degrees to a physical resource, counting each
candidate once when its own physical resources are distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq B]

theorem physical_resource_degree_eq_typed_fibers
    (φ:A→B) (R:C→Finset A) (w:C→ℝ)
    (hinj:∀c,Set.InjOn φ (↑(R c):Set A)) (x:B):
    (∑c,if x∈(R c).image φ then w c else 0)=
      ∑a∈Finset.univ.filter (fun a=>φ a=x),∑c,if a∈R c then w c else 0 :=by
  let X:=Finset.univ.filter (fun a=>φ a=x)
  have hterm (c:C):
      (if x∈(R c).image φ then w c else 0)=∑a∈X,if a∈R c then w c else 0 :=by
    by_cases h:x∈(R c).image φ
    · obtain ⟨a,ha,hax⟩:=Finset.mem_image.mp h
      have haX:a∈X:=by simp [X,hax]
      rw [Finset.sum_eq_single a]
      · simp [h,ha]
      · intro b hbX hba
        have hbx:φ b=x:=(Finset.mem_filter.mp hbX).2
        have hb:¬b∈R c:=by
          intro hb
          have heq:b=a:=hinj c hb ha (hbx.trans hax.symm)
          exact hba heq
        simp [hb]
      · intro hn
        exact (hn haX).elim
    · have hh:∀a∈X,a∉R c:=by
        intro a haX ha
        apply h
        exact Finset.mem_image.mpr ⟨a,ha,(Finset.mem_filter.mp haX).2⟩
      simp only [h,ite_false]
      symm
      apply Finset.sum_eq_zero
      intro a ha
      simp [hh a ha]
  calc
    _ = ∑c,∑a∈X,if a∈R c then w c else 0 := Finset.sum_congr rfl (fun c _=>hterm c)
    _ = _ := by rw [Finset.sum_comm]
end Oberwolfach
