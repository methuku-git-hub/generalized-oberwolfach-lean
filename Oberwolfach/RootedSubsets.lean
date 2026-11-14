module

public import Oberwolfach.SubsetInclusion
public import Oberwolfach.NormalizedSubsetCounts
public import Oberwolfach.UniformConditioning

@[expose] public section

/-! The exact fixed-size subset law after requiring a fixed set of roots.
The remaining labels are sampled without replacement from the complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev RootedSubset (V : Type*) (T : Finset V) (k : ℕ) :=
  {S : FixedSubset V (T.card+k) // T⊆S.val}

def rootedSubsetUnion {V : Type*} [DecidableEq V] (T : Finset V) {k : ℕ}
    (S : FixedSubset {x : V // x∉T} k) : RootedSubset V T k :=
  ⟨⟨T∪S.val.map (Function.Embedding.subtype _),by
    rw [Finset.card_union_of_disjoint,Finset.card_map,S.property]
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hx'
    subst x
    exact y.property hx⟩,Finset.subset_union_left⟩

def rootedSubsetFree {V : Type*} [DecidableEq V] (T : Finset V) {k : ℕ}
    (S : RootedSubset V T k) : FixedSubset {x : V // x∉T} k :=
  ⟨S.val.val.subtype (fun x => x∉T),by
    rw [Finset.card_subtype]
    have he : S.val.val.filter (fun x => x∉T)=S.val.val\T := by
      ext x
      simp
    rw [he,Finset.card_sdiff_of_subset S.property,S.val.property]
    omega⟩

def rootedSubsetEquiv {V : Type*} [DecidableEq V] (T : Finset V) (k : ℕ) :
    RootedSubset V T k ≃ FixedSubset {x : V // x∉T} k where
  toFun := rootedSubsetFree T
  invFun := rootedSubsetUnion T
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    simp only [rootedSubsetUnion,rootedSubsetFree,Finset.mem_union,Finset.mem_map,
      Function.Embedding.coe_subtype,Finset.mem_subtype]
    constructor
    · rintro (hx|⟨y,hy,hyx⟩)
      · exact S.property hx
      · simpa only [hyx] using hy
    · intro hx
      by_cases ht : x∈T
      · exact Or.inl ht
      · exact Or.inr ⟨⟨x,ht⟩,hx,rfl⟩
  right_inv S := by
    apply Subtype.ext
    ext x
    simp [rootedSubsetUnion,rootedSubsetFree,x.property]

theorem rootedSubset_uniform_free {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (k : ℕ) [Nonempty (RootedSubset V T k)]
    [Nonempty (FixedSubset {x : V // x∉T} k)] :
    (FiniteLaw.uniform (RootedSubset V T k)).map (rootedSubsetFree T)=
      FiniteLaw.uniform (FixedSubset {x : V // x∉T} k) :=
  finiteLaw_uniform_map_equiv (rootedSubsetEquiv T k)

theorem rootedSubset_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V) :
    Nonempty (RootedSubset V T k) := by
  have hc : Fintype.card {x : V // x∉T}=Fintype.card V-T.card := by
    rw [Fintype.card_subtype_compl]
    simp
  obtain ⟨S⟩ := fixedSubset_nonempty (V:={x : V // x∉T}) (r:=k) (by rw [hc];omega)
  exact ⟨rootedSubsetUnion T S⟩

theorem rootedSubset_intersection_count {V : Type*} [Fintype V] [DecidableEq V]
    (T A : Finset V) {k : ℕ} (S : FixedSubset {x : V // x∉T} k) :
    (A∩(rootedSubsetUnion T S).val.val).card=
      (A∩T).card+((A.subtype (fun x => x∉T))∩S.val).card := by
  have he : A∩(rootedSubsetUnion T S).val.val=
      (A∩T)∪(((A.subtype (fun x => x∉T))∩S.val).map (Function.Embedding.subtype _)) := by
    ext x
    simp only [rootedSubsetUnion,Finset.mem_inter,Finset.mem_union,Finset.mem_map,
      Function.Embedding.coe_subtype,Finset.mem_subtype]
    constructor
    · rintro ⟨ha,ht|⟨y,hy,hyx⟩⟩
      · exact Or.inl ⟨ha,ht⟩
      · exact Or.inr ⟨y,⟨by simpa only [hyx] using ha,hy⟩,hyx⟩
    · rintro (⟨ha,ht⟩|⟨y,⟨ha,hy⟩,hyx⟩)
      · exact ⟨ha,Or.inl ht⟩
      · exact ⟨by simpa only [hyx] using ha,Or.inr ⟨y,hy,hyx⟩⟩
  rw [he,Finset.card_union_of_disjoint,Finset.card_map]
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨y,hy,hyx⟩ := Finset.mem_map.mp hx'
  subst x
  exact y.property (Finset.mem_inter.mp hx).2

end Oberwolfach
