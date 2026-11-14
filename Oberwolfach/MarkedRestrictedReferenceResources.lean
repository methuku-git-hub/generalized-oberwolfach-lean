module

public import Oberwolfach.MarkedRestrictedFiniteImages

@[expose] public section

/-! The reference sample on a nested invariant pair is exactly the
induced resource set of the original sample. This concerns the fixed
reference, before any adaptive deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_restricted_reference_resources
    (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hf : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (I : Finset V) (J : Finset U) (hI : ∀ x,π x∈I↔x∈I)
    (hfi : Finset.univ.image f=I) (hgj : Finset.univ.image g=J) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) false
    let K₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) true;
    (markedFiniteResources (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:K₀=>a.val.1) (fun a=>a.val.2) ρ Finset.univ
      (Finset.univ.filter (fun z:W×Z=>H false (f z.1) (g z.2)∨H true (f z.1) (g z.2)))).image
      (markedResourceEmbedding f.toEmbedding g)=
    (markedFiniteResources (fun a:E=>a.val.1) (fun a=>a.val.2)
      (fun a:K=>a.val.1) (fun a=>a.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))).filter (markedInnerResource I J) := by
  intro E K E₀ K₀
  let e := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
  let k := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
  let A := Finset.univ.filter (fun a:E⊕K=>
    Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈I ∧
    Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈I)
  let S := (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)).filter
    (fun z=>z.1∈I∧z.2∈J)
  obtain ⟨hAi,hSi⟩ := marked_restricted_finite_images f g π ρ hf P d σ A S
    (by intro a ha;simpa only [hfi] using (Finset.mem_filter.mp ha).2)
    (by intro z hz;simpa only [hfi,hgj] using (Finset.mem_filter.mp hz).2)
  have hfI (x : W) : f x∈I := hfi ▸ Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  have hgJ (u : Z) : g u∈J := hgj ▸ Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
  have hApre : Finset.univ.filter (fun a:E₀⊕K₀=>(e.sumMap k) a∈A)=Finset.univ := by
    apply Finset.filter_true_of_mem
    intro a _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases a with
    | inl a=>exact ⟨hfI a.val.1,hfI a.val.2⟩
    | inr a=>exact ⟨hfI a.val.1,hfI a.val.2⟩
  have hSpre : Finset.univ.filter (fun z:W×Z=>Prod.map f g z∈S)=
      Finset.univ.filter (fun z:W×Z=>H false (f z.1) (g z.2)∨H true (f z.1) (g z.2)) := by
    ext z
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Prod.map_fst,Prod.map_snd,hfI,hgJ,and_self,and_true]
  change (Finset.univ.filter (fun a:E₀⊕K₀=>(e.sumMap k) a∈A)).image (e.sumMap k)=A at hAi
  rw [hApre] at hAi
  rw [hSpre] at hSi
  have hSi' : (Finset.univ.filter (fun z:W×Z=>H false (f z.1) (g z.2)∨H true (f z.1) (g z.2))).image
      (Prod.map f.toEmbedding g)=S := hSi
  have hr := markedFiniteResources_embedding
    (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:K₀=>a.val.1) (fun a=>a.val.2)
    (fun a:E=>a.val.1) (fun a=>a.val.2) (fun a:K=>a.val.1) (fun a=>a.val.2)
    f.toEmbedding g ρ π hf e k (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    Finset.univ (Finset.univ.filter (fun z:W×Z=>H false (f z.1) (g z.2)∨H true (f z.1) (g z.2)))
  rw [hAi,hSi'] at hr
  exact hr.trans (markedFiniteResources_inner _ _ _ _ π Finset.univ _ I J hI)

end Oberwolfach
