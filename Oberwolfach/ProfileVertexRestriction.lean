module

public import Oberwolfach.ResourceRestriction
public import Oberwolfach.ResourceVertexDeletion
public import Oberwolfach.ProfileRootSampling

@[expose] public section

/-! Delete a prescribed vertex set class by class. The induced family
consists exactly of original resource identifiers avoiding that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

abbrev ProfileRemainingClass (Z : Finset (Σ i,V i)) (i : I) :=
  {v : V i // (⟨i,v⟩ : Σ i,V i)∉Z}

def profileComplementEmbedding (Z : Finset (Σ i,V i)) :
    (Σ i,ProfileRemainingClass Z i) ↪ (Σ i,V i) where
  toFun v := ⟨v.1,v.2.val⟩
  inj' := by
    rintro ⟨i,v⟩ ⟨j,w⟩ he
    have hij : i=j := congrArg Sigma.fst he
    subst j
    have hvw : v.val=w.val := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    have hvw' : v=w := Subtype.ext hvw
    subst w
    rfl

theorem profileComplementEmbedding_range (Z : Finset (Σ i,V i)) (v : Σ i,V i) :
    (∃ w,profileComplementEmbedding Z w=v) ↔ v∉Z := by
  constructor
  · rintro ⟨⟨i,w⟩,rfl⟩;exact w.property
  · rcases v with ⟨i,v⟩
    intro hv;exact ⟨⟨i,⟨v,hv⟩⟩,rfl⟩

theorem profileRemainingClass_card (Z : Finset (Σ i,V i)) (i : I) :
    Fintype.card (ProfileRemainingClass Z i)=Fintype.card (V i)-
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)).card := by
  rw [Fintype.card_subtype_compl,Fintype.card_subtype]

theorem profileRemainingClass_profile (a : I → ℕ) (k q : ℕ) (Z : Finset (Σ i,V i))
    (hn : ∀ i,Fintype.card (V i)=a i*k)
    (hZ : ∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)).card=a i*q) (i : I) :
    Fintype.card (ProfileRemainingClass Z i)=a i*(k-q) := by
  rw [profileRemainingClass_card,hn,hZ,← Nat.mul_sub_left_distrib]

theorem profile_resource_survives_iff {C : Type*} (R : C → Finset (Σ i,V i))
    (Z : Finset (Σ i,V i)) (C₀ : C) :
    (∀ v∈R C₀,∃ w,profileComplementEmbedding Z w=v) ↔ Disjoint (R C₀) Z := by
  simp only [profileComplementEmbedding_range]
  exact Finset.disjoint_left.symm

theorem profile_restricted_resource_class_card {C : Type*} [Fintype C] [DecidableEq C]
    (R : C → Finset (Σ i,V i)) (Z : Finset (Σ i,V i))
    (D : RestrictedResource R (profileComplementEmbedding Z)) (i : I) :
    (Finset.univ.filter (fun v : ProfileRemainingClass Z i =>
      (⟨i,v⟩ : Σ i,ProfileRemainingClass Z i)∈restrictedResourceSet R (profileComplementEmbedding Z) D)).card=
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R D.val)).card := by
  let A := {v : ProfileRemainingClass Z i //
    (⟨i,v⟩ : Σ i,ProfileRemainingClass Z i)∈restrictedResourceSet R (profileComplementEmbedding Z) D}
  let B := {v : V i // (⟨i,v⟩ : Σ i,V i)∈R D.val}
  let f (v : A) : B := ⟨v.val.val,(restrictedResourceSet_mem R _ D _).mp v.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : B => z.val) he
    · intro v
      have hv : (⟨i,v.val⟩ : Σ i,V i)∉Z :=
        (profileComplementEmbedding_range Z _).mp (D.property _ v.property)
      refine ⟨⟨⟨v.val,hv⟩,?_⟩,rfl⟩
      exact (restrictedResourceSet_mem R _ D _).mpr v.property
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [A,B,Fintype.card_subtype] using hh

theorem profile_restricted_resource_degree {C : Type*} [Fintype C] [DecidableEq C]
    (R : C → Finset (Σ i,V i)) (Z : Finset (Σ i,V i)) (w : C → ℝ)
    (v : Σ i,ProfileRemainingClass Z i) :
    hypergraphWeightedDegree (restrictedResourceSet R (profileComplementEmbedding Z)) (fun D => w D.val) v=
      hypergraphWeightedDegree R (vertexRestrictedWeight R w Z) (profileComplementEmbedding Z v) := by
  rw [restricted_resource_degree]
  congr 1
  funext C₀
  simp only [profile_resource_survives_iff,vertexRestrictedWeight]

end Oberwolfach
