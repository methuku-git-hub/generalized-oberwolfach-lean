module

public import Oberwolfach.MarkedRestrictedFiniteImages
public import Oberwolfach.MarkedFiniteDivisibilityReflection
public import Oberwolfach.MarkedFiniteDomainBalanceEmbedding

@[expose] public section

/-! Reindex the actual remainder, with its four exact integer balances,
on the next vertex pair. All finite resources and opposite-endpoint balance
values are transported by their specified embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_restricted_finite_remainder
    (f : W↪oV) (g : Z↪U) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
    (hf : ∀ x,f (ρ x)=π (f x)) (P : SimpleGraph V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (HK : V→U→Prop) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) false
    let K₀ := MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>rawMarkedRestrictPair f g σ (Sum.inl e)) true
    let e := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
    let k := markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true;
    ∀ (A : Finset (E⊕K)) (S : Finset (V×U)),
    (∀ a∈A,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈Finset.univ.image f ∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈Finset.univ.image f)→
    (∀ s∈S,s.1∈Finset.univ.image f ∧ s.2∈Finset.univ.image g)→
    MarkedRemainderDivisible (fun a:E=>a.val.1) (fun a=>a.val.2)
      (fun a:K=>a.val.1) (fun a=>a.val.2) HK A S m→
    let A₀ := Finset.univ.filter (fun a:E₀⊕K₀=>(e.sumMap k) a∈A)
    let S₀ := Finset.univ.filter (fun z:W×Z=>Prod.map f g z∈S);
    MarkedRemainderDivisible (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:K₀=>a.val.1) (fun a=>a.val.2) (fun v u=>HK (f v) (g u)) A₀ S₀ m ∧
    (markedFiniteResources (fun a:E₀=>a.val.1) (fun a=>a.val.2)
      (fun a:K₀=>a.val.1) (fun a=>a.val.2) ρ A₀ S₀).image (markedResourceEmbedding f.toEmbedding g)=
      markedFiniteResources (fun a:E=>a.val.1) (fun a=>a.val.2)
        (fun a:K=>a.val.1) (fun a=>a.val.2) π A S ∧
    ∀ (X : Finset W) (Y : Finset Z) (I : Finset V) (J : Finset U),
      (∀ x,f x∈I↔x∈X)→(∀ u,g u∈J↔u∈Y)→∀ z i,
      markedFiniteDomainBalance (fun a:E=>a.val.1) (fun a=>a.val.2)
        (fun a:K=>a.val.1) (fun a=>a.val.2) HK A S m I J (Sum.map f g z) i=
      markedFiniteDomainBalance (fun a:E₀=>a.val.1) (fun a=>a.val.2)
        (fun a:K₀=>a.val.1) (fun a=>a.val.2) (fun v u=>HK (f v) (g u)) A₀ S₀ m X Y z i := by
  intro E K E₀ K₀ e k A S hA hS hdiv A₀ S₀
  obtain ⟨hAi,hSi⟩ := marked_restricted_finite_images f g π ρ hf P d σ A S hA hS
  change A₀.image (e.sumMap k)=A at hAi
  change S₀.image (Prod.map f g)=S at hSi
  have hSi' : S₀.image (Prod.map f.toEmbedding g)=S := hSi
  have hd := marked_finite_divisibility_reflects
    (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:K₀=>a.val.1) (fun a=>a.val.2)
    (fun a:E=>a.val.1) (fun a=>a.val.2) (fun a:K=>a.val.1) (fun a=>a.val.2)
    (fun v u=>HK (f v) (g u)) HK f.toEmbedding g e k
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) A₀ S₀ m (fun _ _=>Iff.rfl)
    (by rw [hAi,hSi'];exact hdiv)
  refine ⟨hd,?_,?_⟩
  · have hr := markedFiniteResources_embedding
      (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:K₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E=>a.val.1) (fun a=>a.val.2) (fun a:K=>a.val.1) (fun a=>a.val.2)
      f.toEmbedding g ρ π hf e k (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) A₀ S₀
    rw [hAi,hSi'] at hr
    exact hr
  · intro X Y I J hX hY z i
    have hb := markedFiniteDomainBalance_embedding
      (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:K₀=>a.val.1) (fun a=>a.val.2)
      (fun a:E=>a.val.1) (fun a=>a.val.2) (fun a:K=>a.val.1) (fun a=>a.val.2)
      (fun v u=>HK (f v) (g u)) HK f.toEmbedding g e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) A₀ S₀ m (fun _ _=>Iff.rfl)
      X Y I J hX hY z i
    rw [hAi,hSi'] at hb
    exact hb

end Oberwolfach
