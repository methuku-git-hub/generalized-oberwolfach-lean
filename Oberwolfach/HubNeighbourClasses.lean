module

public import Oberwolfach.MarkedHubFactor

@[expose] public section

/-! The two actual neighbour classes of a hub and their embedding into
the unchanged ambient vertex set. Spoke-type disjointness gives injectivity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A U : Type*} [Fintype A] [DecidableEq A]

def hubNeighbourClass (H₀ Hₖ : A → U → Prop) (w : U) (i : Bool) :=
  {v : A // if i then Hₖ v w else H₀ v w}

noncomputable instance hubNeighbourClass_fintype (H₀ Hₖ : A → U → Prop) (w : U) (i : Bool) :
    Fintype (hubNeighbourClass H₀ Hₖ w i) := inferInstanceAs (Fintype {v : A // if i then Hₖ v w else H₀ v w})

noncomputable instance hubNeighbourClass_decidableEq (H₀ Hₖ : A → U → Prop) (w : U) (i : Bool) :
    DecidableEq (hubNeighbourClass H₀ Hₖ w i) := Classical.decEq _

def hubNeighbourEmbedding (H₀ Hₖ : A → U → Prop) (w : U)
    (hd : ∀ v,¬(H₀ v w ∧ Hₖ v w)) : (Σ i,hubNeighbourClass H₀ Hₖ w i) ↪ A where
  toFun v := v.2.val
  inj' := by
    rintro ⟨i,v⟩ ⟨j,z⟩ he
    change v.val=z.val at he
    cases i <;> cases j
    · exact congrArg (Sigma.mk false) (Subtype.ext he)
    · exact (hd v.val ⟨v.property,he.symm ▸ z.property⟩).elim
    · exact (hd v.val ⟨he.symm ▸ z.property,v.property⟩).elim
    · exact congrArg (Sigma.mk true) (Subtype.ext he)

theorem hubNeighbourEmbedding_type (H₀ Hₖ : A → U → Prop) (w : U)
    (hd : ∀ v,¬(H₀ v w ∧ Hₖ v w)) (i : Bool) (v : A) :
    (if i then Hₖ v w else H₀ v w) ↔
      ∃ z : hubNeighbourClass H₀ Hₖ w i,hubNeighbourEmbedding H₀ Hₖ w hd ⟨i,z⟩=v := by
  constructor
  · intro hv;exact ⟨⟨v,hv⟩,rfl⟩
  · rintro ⟨z,hz⟩
    change z.val=v at hz
    exact hz ▸ z.property

theorem hubNeighbourEmbedding_image (H₀ Hₖ : A → U → Prop) (w : U)
    (hd : ∀ v,¬(H₀ v w ∧ Hₖ v w)) :
    Finset.univ.image (hubNeighbourEmbedding H₀ Hₖ w hd)=Finset.univ.filter (fun v => H₀ v w ∨ Hₖ v w) := by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ⟨⟨i,z⟩,hz⟩
    cases i
    · exact Or.inl (hz ▸ z.property)
    · exact Or.inr (hz ▸ z.property)
  · rintro (h0|hK)
    · exact ⟨⟨false,⟨v,h0⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨v,hK⟩⟩,rfl⟩

end Oberwolfach
