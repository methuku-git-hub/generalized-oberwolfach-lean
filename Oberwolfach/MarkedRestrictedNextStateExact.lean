module

public import Oberwolfach.MarkedRestrictedFiniteImages
public import Oberwolfach.MarkedFiniteResourcesEmbedding
public import Oberwolfach.MarkedReferenceStateRemainder

@[expose] public section
/-! A remainder supported on the next embedded pair determines a deletion
state of the restricted fixed sample, with precisely the same resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_restricted_next_state_exact
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ₀:=rawMarkedRestrictPair f g σ
    let H₀:=fun b x u=>H b (f x) (g u)
    let E₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K₀:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim (fun a:E=>a.val.1) (fun a:K=>a.val.1) a∈Finset.univ.image f∧
      Sum.elim (fun a:E=>a.val.2) (fun a:K=>a.val.2) a∈Finset.univ.image f)→
    (∀ z∈S,z.1∈Finset.univ.image f∧z.2∈Finset.univ.image g∧(H false z.1 z.2∨H true z.1 z.2))→
    ∃ T:MarkedReferenceDeletion (P.comap f) ρ d σ₀,
      (T.remaining H₀).image (markedResourceEmbedding f.toEmbedding g)=
        markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π A S:=by
  intro E K σ₀ H₀ E₀ K₀ A S hA hS
  let e:E₀↪E:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ false
  let k:K₀↪K:=markedRestrictedSampleArcEmbedding f g π ρ hf P d σ true
  let A₀:Finset (E₀⊕K₀):=Finset.univ.filter (fun a=>(e.sumMap k) a∈A)
  let S₀:Finset (W×Z):=Finset.univ.filter (fun z=>Prod.map f g z∈S)
  let Sfull:Finset (W×Z):=Finset.univ.filter (fun z=>H₀ false z.1 z.2∨H₀ true z.1 z.2)
  have hSi:S₀⊆Sfull:=by
    intro z hz
    have hzS:Prod.map f g z∈S:=(Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hS _ hzS).2.2⟩
  have himg:=marked_restricted_finite_images f g π ρ hf P d σ A S hA
    (by intro z hz;exact ⟨(hS z hz).1,(hS z hz).2.1⟩)
  change A₀.image (e.sumMap k)=A ∧ S₀.image (Prod.map f g)=S at himg
  let T:MarkedReferenceDeletion (P.comap f) ρ d σ₀:=⟨Finset.univ\A₀,Sfull\S₀⟩
  refine ⟨T,?_⟩
  have hrem:T.remaining H₀=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:K₀=>e.val.1) (fun e=>e.val.2) ρ A₀ S₀:=by
    rw [T.remaining_eq H₀]
    have hAA:Finset.univ\T.arcs=A₀:=by
      change Finset.univ\(Finset.univ\A₀)=A₀
      ext a;simp
    have hSS:Sfull\T.spokes=S₀:=by
      change Sfull\(Sfull\S₀)=S₀
      ext z
      simp only [Finset.mem_sdiff]
      constructor
      · intro hh;by_contra h;exact hh.2 ⟨hh.1,h⟩
      · intro hz;exact ⟨hSi hz,by tauto⟩
    rw [hAA,hSS]
  rw [hrem]
  have heq:=markedFiniteResources_embedding (fun e:E₀=>e.val.1) (fun e=>e.val.2)
    (fun e:K₀=>e.val.1) (fun e=>e.val.2) (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) f.toEmbedding g ρ π hf e k
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) A₀ S₀
  have hSi':S₀.image (Prod.map f.toEmbedding g)=S:=himg.2
  rw [himg.1,hSi'] at heq
  exact heq
end Oberwolfach
