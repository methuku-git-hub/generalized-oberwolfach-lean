module

public import Oberwolfach.RootedSubsets
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! The conditional law after requiring specified vertices in each
class sample is exactly uniform on the remaining class populations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_uniform {I : Type*} [Fintype I] [DecidableEq I]
    {D : I → Type*} [∀ i,Fintype (D i)] [∀ i,Nonempty (D i)] :
    FiniteLaw.pi (fun i => FiniteLaw.uniform (D i))=FiniteLaw.uniform (∀ i,D i) := by
  apply finiteLaw_ext
  intro σ
  simp [FiniteLaw.pi,FiniteLaw.uniform,Fintype.card_pi,Nat.cast_prod,Finset.prod_div_distrib]

variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

def fillProfileRoots (T : ∀ i,Finset (V i)) {k : I → ℕ}
    (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) :
    ∀ i,FixedSubset (V i) ((T i).card+k i) :=
  fun i => (rootedSubsetUnion (T i) (σ i)).val

def profileRootConditionEquiv (T : ∀ i,Finset (V i)) (k : I → ℕ) :
    (∀ i,FixedSubset {v : V i // v∉T i} (k i)) ≃
      {σ : ∀ i,FixedSubset (V i) ((T i).card+k i) // ∀ i,T i⊆(σ i).val} where
  toFun σ := ⟨fillProfileRoots T σ,fun i => (rootedSubsetUnion (T i) (σ i)).property⟩
  invFun σ := fun i => rootedSubsetFree (T i) ⟨σ.val i,σ.property i⟩
  left_inv σ := by
    funext i
    exact (rootedSubsetEquiv (T i) (k i)).apply_symm_apply (σ i)
  right_inv σ := by
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val ((rootedSubsetEquiv (T i) (k i)).symm_apply_apply ⟨σ.val i,σ.property i⟩)

theorem profile_root_conditional_probability (T : ∀ i,Finset (V i)) (k : I → ℕ)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (k i))]
    [∀ i,Nonempty (FixedSubset (V i) ((T i).card+k i))]
    (Bad : (∀ i,FixedSubset (V i) ((T i).card+k i)) → Prop) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) ((T i).card+k i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))
    μ.probability (fun σ => (∀ i,T i⊆(σ i).val) ∧ Bad σ)=
      μ.probability (fun σ => ∀ i,T i⊆(σ i).val)*ν.probability (fun σ => Bad (fillProfileRoots T σ)) := by
  let e := profileRootConditionEquiv T k
  letI : Nonempty {σ : ∀ i,FixedSubset (V i) ((T i).card+k i) // ∀ i,T i⊆(σ i).val} :=
    ⟨e (Classical.choice inferInstance)⟩
  simp only [finiteLaw_pi_uniform]
  rw [uniform_probability_intersection]
  have he := finiteLaw_uniform_map_equiv e
  have hp := finiteLaw_map_probability
    (FiniteLaw.uniform (∀ i,FixedSubset {v : V i // v∉T i} (k i))) e
    (fun σ => Bad σ.val)
  rw [he] at hp
  rw [hp]
  rfl

end Oberwolfach
