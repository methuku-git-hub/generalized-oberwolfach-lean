module

public import Oberwolfach.MarkedRestrictedSampleResources

@[expose] public section

/-! A remaining arc and spoke set supported on fixed embedded domains has
an exact preimage in the restricted sample. The original occurrence IDs
are preserved by the two sample embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_restricted_finite_images
    (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hf : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let e := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
    let k := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true;
    ∀ (A : Finset (E⊕K)) (S : Finset (V×U)),
    (∀ a∈A,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈Finset.univ.image f ∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈Finset.univ.image f)→
    (∀ s∈S,s.1∈Finset.univ.image f ∧ s.2∈Finset.univ.image g)→
    (Finset.univ.filter (fun a=>(e.sumMap k) a∈A)).image (e.sumMap k)=A ∧
    (Finset.univ.filter (fun z:W×Z=>Prod.map f g z∈S)).image (Prod.map f g)=S := by
  intro E K e k A S hA hS
  have hRange (j : Bool) (a : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) j)
      (ha : a.val.1∈Finset.univ.image f ∧ a.val.2∈Finset.univ.image f) :
      ∃ b,markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j b=a := by
    have h : a∈Finset.univ.image (markedRestrictedSampleArcEmbedding f g π ρ hf P d σ j) := by
      rw [markedRestrictedSampleArcEmbedding_range]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    obtain ⟨b,_,hb⟩ := Finset.mem_image.mp h
    exact ⟨b,hb⟩
  constructor
  · ext a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp hb).2
    · intro ha
      have hs := hA a ha
      cases a with
      | inl a =>
        obtain ⟨b,hb⟩ := hRange false a hs
        refine Finset.mem_image.mpr ⟨Sum.inl b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
        · change Sum.inl (e b)∈A
          change e b=a at hb
          rw [hb]
          exact ha
        · exact congrArg Sum.inl hb
      | inr a =>
        obtain ⟨b,hb⟩ := hRange true a hs
        refine Finset.mem_image.mpr ⟨Sum.inr b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
        · change Sum.inr (k b)∈A
          change k b=a at hb
          rw [hb]
          exact ha
        · exact congrArg Sum.inr hb
  · ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ha).2
    · intro hz
      obtain ⟨hv,hu⟩ := hS z hz
      obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hv
      obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hu
      have he : Prod.map f g (v,u)=z := Prod.ext hv hu
      exact Finset.mem_image.mpr ⟨(v,u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hz⟩,he⟩

end Oberwolfach
