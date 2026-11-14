module

public import Oberwolfach.OrdinaryHostDecompositions

@[expose] public section

/-! Recover a decomposition in the actual host from displayed universal
wheels, checking both physical containment and the forbidden-pair condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U] {r : ℕ}

def ordinaryWheelInHost (Q F : SimpleGraph V) (H : V → U → Prop)
    (W : UniversalOrdinaryWheel V U r)
    (hW : ordinaryWheelResources W⊆ordinaryHostResources Q H)
    (hF : ∀ v∈(ordinaryWheelRim W).support,∀ w∈(ordinaryWheelRim W).support,¬F.Adj v w) :
    OrdinaryWheel Q F H r :=
  ⟨(⟨W.val.1.val,((ordinaryWheelResources_subset_host W Q H).mp hW).1⟩,ordinaryWheelHub W),
    ((ordinaryWheelResources_subset_host W Q H).mp hW).2,hF⟩

theorem ordinary_decomposition_recover_host (Q F : SimpleGraph V) (H : V → U → Prop)
    (L : Finset (Sym2 V⊕(V×U))) (hL : L⊆ordinaryHostResources Q H)
    (D : Finset (UniversalOrdinaryWheel V U r))
    (hD : (∀ W∈D,∀ W'∈D,W≠W'→Disjoint (ordinaryWheelResources W) (ordinaryWheelResources W')) ∧
      D.biUnion ordinaryWheelResources=L)
    (hF : ∀ W∈D,∀ v∈(ordinaryWheelRim W).support,∀ w∈(ordinaryWheelRim W).support,¬F.Adj v w) :
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L := by
  have hsub (W : D) : ordinaryWheelResources W.val⊆ordinaryHostResources Q H := by
    intro e he
    apply hL
    rw [←hD.2]
    exact Finset.mem_biUnion.mpr ⟨W.val,W.property,he⟩
  let f : D → OrdinaryWheel Q F H r := fun W=>ordinaryWheelInHost Q F H W.val (hsub W) (hF W.val W.property)
  refine ⟨Finset.univ.image f,?_,?_⟩
  · intro A hA B hB hAB
    obtain ⟨W,_,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨W',_,rfl⟩ := Finset.mem_image.mp hB
    exact hD.1 W.val W.property W'.val W'.property (fun he=>hAB (congrArg f (Subtype.ext he)))
  · ext e
    rw [←hD.2]
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨W,⟨W',rfl⟩,he⟩
      exact ⟨W'.val,W'.property,he⟩
    · rintro ⟨W,hW,he⟩
      exact ⟨f ⟨W,hW⟩,⟨⟨W,hW⟩,rfl⟩,he⟩

end Oberwolfach
