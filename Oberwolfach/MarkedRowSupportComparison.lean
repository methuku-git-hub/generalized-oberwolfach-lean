module

public import Oberwolfach.MarkedResourceSupport
public import Oberwolfach.MarkedWheelFamilyLoads

@[expose] public section

/-! Comparison hosts in successive row covers. Resource intersections are
pulled back through the injective physical map, so a shifted physical head
does not get confused with the auxiliary row at which the arc ends. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : K→V} {π : Equiv.Perm V}

theorem marked_resource_supported_inter
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A B : Finset V) (e : Finset V⊕(V×U))
    (hA : MarkedResourceSupported tail head ktail khead π A e)
    (hB : MarkedResourceSupported tail head ktail khead π B e) :
    MarkedResourceSupported tail head ktail khead π (A∩B) e := by
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩ := hA
    obtain ⟨b,hb,hbt,hbh⟩ := hB
    have hab : a=b := hp (ha.trans hb.symm)
    subst b
    exact ⟨a,ha,Finset.mem_inter.mpr ⟨hat,hbt⟩,Finset.mem_inter.mpr ⟨hah,hbh⟩⟩
  | inr vu=>exact Finset.mem_inter.mpr ⟨hA,hB⟩

theorem marked_wheel_resources_supported {m b : ℕ} {H₀ HK : V→U→Prop}
    (C : MarkedWheel tail head ktail khead m π b H₀ HK) (A : Finset V)
    (hA : markedWheelRows C⊆A) :
    ∀ e∈markedWheelPhysicalResources C,MarkedResourceSupported tail head ktail khead π A e := by
  intro e he
  have hh := marked_cycle_at_hub_supported C.1 C.2.val A
    (fun i=>hA (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)) e
  apply hh
  cases e with
  | inl e=>
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨e,(markedWheelPhysicalResources_rim C e).mp he,rfl⟩
  | inr vu=>
    obtain ⟨hu,hv⟩ := (markedWheelPhysicalResources_spoke C vu.1 vu.2).mp he
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨vu.1,hv,by rw [hu]⟩

theorem marked_row_cover_preserves_other_root {m b : ℕ} {H₀ HK : V→U→Prop}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedWheel tail head ktail khead m π b H₀ HK)
    (F : Finset V) (v w : V) (hwv : w≠v) (hwF : w∉F)
    (hrows : markedWheelRows C⊆insert v F) :
    (∀ a : E⊕K,Sum.elim tail ktail a=w ∨ Sum.elim head khead a=w →
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉markedWheelPhysicalResources C) ∧
    (∀ u,Sum.inr (w,u)∉markedWheelPhysicalResources C) := by
  have hw : w∉insert v F := by simpa using And.intro hwv hwF
  constructor
  · intro a ha he
    obtain ⟨b,hb,hbt,hbh⟩ := marked_wheel_resources_supported C (insert v F) hrows _ he
    have hab : b=a := hp hb
    subst b
    rcases ha with ha|ha
    · exact hw (ha ▸ hbt)
    · exact hw (ha ▸ hbh)
  · intro u he
    exact hw (marked_wheel_resources_supported C (insert v F) hrows _ he)

def markedFreeResource (F : Finset V) : Finset V⊕(V×U)→Prop :=
  Sum.elim (fun e=>e⊆F) (fun vu=>vu.1∈F)

theorem marked_supported_resource_is_free (F : Finset V) (hF : ∀ v,π v∈F ↔ v∈F)
    (e : Finset V⊕(V×U)) (he : MarkedResourceSupported tail head ktail khead π F e) :
    markedFreeResource F e := by
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩ := he
    rw [←ha]
    cases a with
    | inl a=>exact Finset.insert_subset_iff.mpr ⟨hat,Finset.singleton_subset_iff.mpr hah⟩
    | inr a=>exact Finset.insert_subset_iff.mpr ⟨hat,Finset.singleton_subset_iff.mpr ((hF _).mpr hah)⟩
  | inr vu=>exact he

theorem marked_row_comparison_resources_disjoint
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (T F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F) (v : V) (hvT : v∉T)
    (hTF : Disjoint T F) (M C : Finset (Finset V⊕(V×U)))
    (hM : ∀ e∈M,MarkedResourceSupported tail head ktail khead π (T∪F) e)
    (hC : ∀ e∈C,MarkedResourceSupported tail head ktail khead π (insert v F) e)
    (hfree : Disjoint C (M.filter (markedFreeResource F))) : Disjoint C M := by
  have hi : (T∪F)∩insert v F⊆F := by
    intro z hz
    obtain ⟨hzT,hzV⟩ := Finset.mem_inter.mp hz
    rcases Finset.mem_union.mp hzT with hzT|hzF
    · rcases Finset.mem_insert.mp hzV with rfl|hzF
      · exact False.elim (hvT hzT)
      · exact False.elim (Finset.disjoint_left.mp hTF hzT hzF)
    · exact hzF
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hsupport := marked_resource_supported_inter hp (T∪F) (insert v F) e (hM e hf) (hC e he)
  have hsmall := marked_resource_support_mono hi e hsupport
  exact Finset.disjoint_left.mp hfree he
    (Finset.mem_filter.mpr ⟨hf,marked_supported_resource_is_free F hF e hsmall⟩)

end Oberwolfach
