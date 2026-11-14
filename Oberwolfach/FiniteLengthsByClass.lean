module

public import Oberwolfach.ComponentFamilyDomainCard

@[expose] public section
/-! Partition a finite collection of objects by their length index. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {A:Type} [Fintype A] {K:ℕ}

theorem finite_lengths_by_class (idx:A→Fin K) (ℓ:Fin K→ℕ):
    (∑a:A,ℓ (idx a)) = ∑i:Fin K,(Finset.univ.filter (fun a:A=>idx a=i)).card * ℓ i :=by
  classical
  have hf:=Finset.sum_fiberwise_of_maps_to (s:=(Finset.univ:Finset A)) (t:=(Finset.univ:Finset (Fin K)))
    (g:=idx) (fun _ _=>Finset.mem_univ _) (fun a=>ℓ (idx a))
  rw [←hf]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = ∑_a:A with idx _a=i,ℓ i := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ :=by simp
end Oberwolfach
