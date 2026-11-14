module

public import Oberwolfach.ProfileConditioning
public import Oberwolfach.ProfileRootSampling

@[expose] public section

/-! The actual vertex set after filling the conditioned roots.
The remaining labels embed in the original classes without relabelling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)]

def profileRootFreeEmbedding (T : ∀ i,Finset (V i)) :
    (Σ i,{v : V i // v∉T i}) ↪ (Σ i,V i) where
  toFun v := ⟨v.1,v.2.val⟩
  inj' := by
    rintro ⟨i,v⟩ ⟨j,w⟩ he
    have hij : i=j := congrArg Sigma.fst he
    subst j
    have hvw : v.val=w.val := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    have hvw' : v=w := Subtype.ext hvw
    subst w
    rfl

theorem profileRootFreeEmbedding_mem (T : ∀ i,Finset (V i)) {k : I → ℕ}
    (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) (i : I) (v : V i) :
    (⟨i,v⟩ : Σ i,V i)∈(profileRootSet σ).map (profileRootFreeEmbedding T) ↔
      ∃ hv : v∉T i,(⟨v,hv⟩ : {v : V i // v∉T i})∈(σ i).val := by
  constructor
  · intro h
    obtain ⟨⟨j,u⟩,hu,he⟩ := Finset.mem_map.mp h
    have hji : j=i := congrArg Sigma.fst he
    subst j
    have huv : u.val=v := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    subst v
    exact ⟨u.property,(profileRootSet_mem σ i u).mp hu⟩
  · rintro ⟨hv,hvσ⟩
    exact Finset.mem_map.mpr ⟨⟨i,⟨v,hv⟩⟩,(profileRootSet_mem σ i ⟨v,hv⟩).mpr hvσ,rfl⟩

theorem fillProfileRoots_ground (T : ∀ i,Finset (V i)) {k : I → ℕ}
    (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) :
    profileRootSet (fillProfileRoots T σ)=
      Finset.univ.sigma T∪(profileRootSet σ).map (profileRootFreeEmbedding T) := by
  ext ⟨i,v⟩
  rw [profileRootSet_mem,Finset.mem_union,profileRootFreeEmbedding_mem]
  simp only [fillProfileRoots,rootedSubsetUnion,Finset.mem_union,Finset.mem_map,
    Function.Embedding.coe_subtype,Finset.mem_sigma,Finset.mem_univ,true_and]
  constructor
  · rintro (hv|⟨u,hu,he⟩)
    · exact Or.inl hv
    · subst v;exact Or.inr ⟨u.property,hu⟩
  · rintro (hv|⟨hv,hu⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨⟨v,hv⟩,hu,rfl⟩

theorem profileRootFreeEmbedding_complement (T : ∀ i,Finset (V i)) :
    Finset.univ.map (profileRootFreeEmbedding T)=Finset.univ\Finset.univ.sigma T := by
  ext ⟨i,v⟩
  constructor
  · intro h
    obtain ⟨⟨j,u⟩,_,he⟩ := Finset.mem_map.mp h
    have hji : j=i := congrArg Sigma.fst he
    subst j
    have huv : u.val=v := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    subst v
    simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_sigma,true_and] using u.property
  · intro h
    have hv : v∉T i := by simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_sigma,true_and] using h
    exact Finset.mem_map.mpr ⟨⟨i,⟨v,hv⟩⟩,Finset.mem_univ _,rfl⟩

end Oberwolfach
