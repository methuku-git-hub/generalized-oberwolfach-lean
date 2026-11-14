module

public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section
/-! The canonical star restriction commutes with the typed sample deletion
embedding, including an arbitrary prescribed arc omission. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_sample_canonical_star_arcs_preimage
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (I T:Finset V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ':=rawMarkedDeleteRims σ D
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let emb:=markedSampleDeletedArcsEmbedding P π d σ D;
    ∀ DA:Finset (E⊕K),
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let CA:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈I∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈I))\DA
    let CA':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim (fun e:E'=>e.val.1) (fun e:K'=>e.val.1) a∈I∧
      Sum.elim (fun e:E'=>e.val.2) (fun e:K'=>e.val.2) a∈I))\DA'
    let KA:=CA.filter (fun a=>Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈T∨
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈T)
    let KA':=CA'.filter (fun a=>Sum.elim (fun e:E'=>e.val.1) (fun e:K'=>e.val.1) a∈T∨
      Sum.elim (fun e:E'=>e.val.2) (fun e:K'=>e.val.2) a∈T);
    KA'=Finset.univ.filter (fun a:E'⊕K'=>emb a∈KA):=by
  intro E K σ' E' K' emb DA DA' CA CA' KA KA'
  ext a
  have hs:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ D a
  simp only [KA',KA,CA',CA,DA',Finset.mem_filter,Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [hs.1,hs.2.1]
end Oberwolfach
