module

public import Oberwolfach.TwoClassRootOrder
public import Oberwolfach.TupleResourceMultiplicity
public import Oberwolfach.ProfileRootPartitionSigma

@[expose] public section

/-! The exact (1,m) class profile and bounded multiplicity of actual
canonical marked cycles on the two hub-neighbour classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {m : ℕ} {V : Bool → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem twoClass_tuple_profile (x : Fin (m+1) → Σ i,V i) (hx : Function.Injective x)
    (hK : (x 0).1=true) (hO : ∀ j : Fin m,(x j.succ).1=false) (i : Bool) :
    (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Finset.univ.image x)).card=
      twoClassProfile m i := by
  rw [← sigma_finset_class_card,Finset.filter_image,Finset.card_image_of_injective _ hx]
  cases i
  · have he : Finset.univ.filter (fun j => (x j).1=false)=Finset.univ.erase 0 := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [hK]
      · simp [hO,Fin.succ_ne_zero]
    rw [he]
    simp [twoClassProfile]
  · have he : Finset.univ.filter (fun j => (x j).1=true)={0} := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [hK]
      · simp [hO,Fin.succ_ne_zero]
    rw [he]
    simp [twoClassProfile]

variable {U E K : Type*} {tail head : E → Σ i,V i} {ktail khead : K → Σ i,V i}
    {π : Equiv.Perm (Σ i,V i)} {b : ℕ} {H₀ Hₖ : (Σ i,V i) → U → Prop}

theorem hubMarkedCycle_profile (w : U)
    (hK : ∀ v,Hₖ v w ↔ v.1=true) (hO : ∀ v,H₀ v w ↔ v.1=false)
    (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) (i : Bool) :
    (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈hubMarkedCycleVertices w C)).card=
      twoClassProfile m i :=
  twoClass_tuple_profile C.val (permutationSeparated_injective π b C.val C.property.1.1)
    ((hK _).mp C.property.2.1) (fun j => (hO _).mp (C.property.2.2 j)) i

theorem hubMarkedCycle_multiplicity (w : U) (Y : Finset (Σ i,V i)) :
    Fintype.card {C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w // hubMarkedCycleVertices w C=Y}≤
      (m+1)^(m+1) := by
  apply tuple_resource_multiplicity (m+1) _ (fun C => C.val) (fun _ _ he => Subtype.ext he)
    (fun _ => rfl) _ Y
  intro C
  change (Finset.univ.image C.val).card=m+1
  rw [Finset.card_image_of_injective _
    (permutationSeparated_injective π b C.val C.property.1.1),Finset.card_univ,Fintype.card_fin]

end Oberwolfach
