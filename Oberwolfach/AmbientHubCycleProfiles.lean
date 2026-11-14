module

public import Oberwolfach.HubCycleProfiles
public import Oberwolfach.SupportedResourceFactors

@[expose] public section

/-! Hub classes are embedded in the ambient vertex set. The successor
permutation is never required to preserve the union of these classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A U E K : Type*} [Fintype A] [DecidableEq A]
    {V : Bool → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {tail head : E → A} {ktail khead : K → A} {m : ℕ}
    {π : Equiv.Perm A} {b : ℕ} {H₀ Hₖ : A → U → Prop}

theorem embedded_class_image_iff (e : (Σ i,V i) ↪ A) (i : Bool) (z : Σ i,V i) :
    (∃ v : V i,e ⟨i,v⟩=e z) ↔ z.1=i := by
  constructor
  · rintro ⟨v,hv⟩
    exact (congrArg Sigma.fst (e.injective hv)).symm
  · rcases z with ⟨j,v⟩
    intro he
    change j=i at he
    subst j
    exact ⟨v,rfl⟩

theorem hubMarkedCycle_supported (e : (Σ i,V i) ↪ A) (w : U)
    (hK : ∀ v,Hₖ v w ↔ ∃ z : V true,e ⟨true,z⟩=v)
    (hO : ∀ v,H₀ v w ↔ ∃ z : V false,e ⟨false,z⟩=v)
    (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) :
    ∀ v∈hubMarkedCycleVertices w C,∃ z,e z=v := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  refine Fin.cases ?_ (fun i => ?_) i
  · obtain ⟨z,hz⟩ := (hK _).mp C.property.2.1
    exact ⟨⟨true,z⟩,hz⟩
  · obtain ⟨z,hz⟩ := (hO _).mp (C.property.2.2 i)
    exact ⟨⟨false,z⟩,hz⟩

theorem ambient_hubMarkedCycle_profile (e : (Σ i,V i) ↪ A) (w : U)
    (hK : ∀ v,Hₖ v w ↔ ∃ z : V true,e ⟨true,z⟩=v)
    (hO : ∀ v,H₀ v w ↔ ∃ z : V false,e ⟨false,z⟩=v)
    (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) (i : Bool) :
    (Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈hubMarkedCycleVertices w C)).card=twoClassProfile m i := by
  have hs := hubMarkedCycle_supported e w hK hO C
  have hf (j : Fin (m+1)) : ∃ z,e z=C.val j := hs _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  let f (j : Fin (m+1)) : Σ i,V i := Classical.choose (hf j)
  have he (j) : e (f j)=C.val j := Classical.choose_spec (hf j)
  have hfi : Function.Injective f := by
    intro j k hjk
    apply permutationSeparated_injective π b C.val C.property.1.1
    rw [← he j,← he k,hjk]
  have hfK : (f 0).1=true := by
    apply (embedded_class_image_iff e true (f 0)).mp
    rw [he 0]
    exact (hK _).mp C.property.2.1
  have hfO (j : Fin m) : (f j.succ).1=false := by
    apply (embedded_class_image_iff e false (f j.succ)).mp
    rw [he j.succ]
    exact (hO _).mp (C.property.2.2 j)
  have hmem (v : Σ i,V i) : e v∈hubMarkedCycleVertices w C ↔ v∈Finset.univ.image f := by
    constructor
    · intro hv
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e.injective ((he j).trans hj)⟩
    · rintro hv
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,(he j).symm⟩
  have hh := twoClass_tuple_profile f hfi hfK hfO i
  simpa only [hmem] using hh

theorem ambient_hubMarkedCycle_multiplicity (w : U) (Y : Finset A) :
    Fintype.card {C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w // hubMarkedCycleVertices w C=Y}≤
      (m+1)^(m+1) := by
  apply tuple_resource_multiplicity (m+1) _ (fun C => C.val) (fun _ _ he => Subtype.ext he)
    (fun _ => rfl) _ Y
  intro C
  change (Finset.univ.image C.val).card=m+1
  rw [Finset.card_image_of_injective _
    (permutationSeparated_injective π b C.val C.property.1.1),Finset.card_univ,Fintype.card_fin]

end Oberwolfach
