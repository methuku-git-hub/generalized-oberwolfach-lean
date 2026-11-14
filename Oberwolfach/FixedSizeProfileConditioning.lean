module

public import Oberwolfach.ProfileConditioning
public import Oberwolfach.ConditionedProfileGeometry

@[expose] public section

/-! Exact conditioning on a root set without changing the original
sample-size notation or the original sample space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

def profileSizeEquiv {m n : I → ℕ} (h : ∀ i,m i=n i) :
    (∀ i,FixedSubset (V i) (m i)) ≃ (∀ i,FixedSubset (V i) (n i)) where
  toFun σ := fun i => ⟨(σ i).val,(σ i).property.trans (h i)⟩
  invFun σ := fun i => ⟨(σ i).val,(σ i).property.trans (h i).symm⟩
  left_inv σ := by funext i;apply Subtype.ext;rfl
  right_inv σ := by funext i;apply Subtype.ext;rfl

theorem profileSizeEquiv_val {m n : I → ℕ} (h : ∀ i,m i=n i)
    (σ : ∀ i,FixedSubset (V i) (m i)) (i : I) :
    ((profileSizeEquiv h σ) i).val=(σ i).val := rfl

theorem profileSizeEquiv_ground {m n : I → ℕ} (h : ∀ i,m i=n i)
    (σ : ∀ i,FixedSubset (V i) (m i)) :
    profileRootSet (profileSizeEquiv h σ)=profileRootSet σ := by
  ext v
  rcases v with ⟨i,v⟩
  exact (profileRootSet_mem (profileSizeEquiv h σ) i v).trans (profileRootSet_mem σ i v).symm

def fillProfileRootsAtSize (T : ∀ i,Finset (V i)) (m : I → ℕ)
    (hT : ∀ i,(T i).card ≤ m i)
    (σ : ∀ i,FixedSubset {v : V i // v∉T i} (m i-(T i).card)) :
    ∀ i,FixedSubset (V i) (m i) :=
  profileSizeEquiv (fun i => Nat.add_sub_of_le (hT i)) (fillProfileRoots T σ)

theorem fillProfileRootsAtSize_ground (T : ∀ i,Finset (V i)) (m : I → ℕ)
    (hT : ∀ i,(T i).card ≤ m i)
    (σ : ∀ i,FixedSubset {v : V i // v∉T i} (m i-(T i).card)) :
    profileRootSet (fillProfileRootsAtSize T m hT σ)=
      Finset.univ.sigma T∪(profileRootSet σ).map (profileRootFreeEmbedding T) := by
  rw [fillProfileRootsAtSize,profileSizeEquiv_ground]
  convert fillProfileRoots_ground T σ using 1 <;> congr!

theorem profile_fixed_size_conditional_probability (T : ∀ i,Finset (V i)) (m : I → ℕ)
    (hT : ∀ i,(T i).card ≤ m i)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (m i-(T i).card))]
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (Bad : (∀ i,FixedSubset (V i) (m i)) → Prop) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (m i-(T i).card)))
    μ.probability (fun σ => (∀ i,T i⊆(σ i).val) ∧ Bad σ)=
      μ.probability (fun σ => ∀ i,T i⊆(σ i).val)*
        ν.probability (fun σ => Bad (fillProfileRootsAtSize T m hT σ)) := by
  let k := fun i => m i-(T i).card
  let n := fun i => (T i).card+k i
  have hn : ∀ i,n i=m i := fun i => Nat.add_sub_of_le (hT i)
  letI : ∀ i,Nonempty (FixedSubset (V i) (n i)) := fun i => by rw [hn i];infer_instance
  let e : (∀ i,FixedSubset (V i) (n i)) ≃ (∀ i,FixedSubset (V i) (m i)) := profileSizeEquiv hn
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
  let μ' := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (n i)))
  have hmap : μ'.map e=μ := by
    dsimp [μ',μ]
    rw [finiteLaw_pi_uniform,finiteLaw_pi_uniform]
    exact finiteLaw_uniform_map_equiv e
  have hp (P : (∀ i,FixedSubset (V i) (m i)) → Prop) :
      μ.probability P=μ'.probability (fun σ => P (e σ)) := by
    rw [← hmap,finiteLaw_map_probability]
  change μ.probability _=μ.probability _*_
  rw [hp,hp]
  have hh := profile_root_conditional_probability T k (fun σ => Bad (e σ))
  simpa only [e,profileSizeEquiv_val,fillProfileRootsAtSize] using hh

end Oberwolfach
