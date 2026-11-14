module

public import Oberwolfach.MarkedVortexInitialSampleChangeData
public import Oberwolfach.MarkedInnerDeepBalanceSeparateBounds

@[expose] public section
/-! The initial parent balance survives the same physical changes that
encode the corrected sample. Both errors retain the ambient scale; only
the inner set needs a relative-size hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_balance_transfer
    (r:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    (∀e,σ (Sum.inr e)=τ (Sum.inr e))→
    (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀v u,¬(H false v u∧H true v u))→(∀v u,¬(H' false v u∧H' true v u))→
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let σ₀:=rawMarkedRestrictPair f g σ
    let τ₀:=rawMarkedRestrictPair f g τ
    let H₀:=fun b v u=>H b (f v) (g u)
    let H₀':=fun b v u=>H' b (f v) (g u)
    let I:=markedVortexInnerVertices Q 0
    let J:=markedVortexInnerHubs Q 0
    let T:=markedVortexDeeperVertices Q 0
    let R:=markedVortexDeeperHubs Q 0
    let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:W×Z=>H₀ false z.1 z.2∨H₀ true z.1 z.2)
    let E':=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) false
    let K':=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun z:W×Z=>H₀' false z.1 z.2∨H₀' true z.1 z.2);
    iota*Fintype.card W≤(I.card:ℝ)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H₀ true) Finset.univ S (r+4) I J v j|≤(x/4)*Fintype.card W)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H₀ true) Finset.univ S (r+4) I J v j|≤(etaBal/2)*I.card)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H₀ true) Finset.univ S (r+4) T R v j|≤(x/4)*Fintype.card W)→
    ∃errI errT:ℝ,0≤errI ∧ 0≤errT ∧ errI≤(x/2)*Fintype.card W ∧ errT≤(x/2)*Fintype.card W ∧
      errI≤etaBal*I.card ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) T R v j|≤errT) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_inner_deep_balance_from_separate_bounds (r+4) etaBal x iota hη hx hi
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ G D m β ε Q π hπ d σ τ H H' FR FS hinterval hR hS hFR hFS hH hH'
    W Z f g ρ σ₀ τ₀ H₀ H₀' I J T R E K S E' K' S' hsize hI hIrel hT
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  rw [hdec] at hI hIrel hT ⊢
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σ τ H H' FR FS ζ hinterval hR hS hFR hFS
  exact htransfer ζ hζ hζcap W Z Γ Color (G.comap f) ρ d I T J R σ₀ τ₀ H₀ H₀'
    (FR.comap f) (FS.comap (Sum.map f g)) hsize
    (by intro v u;exact hH (f v) (g u)) (by intro v u;exact hH' (f v) (g u))
    hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1 hchanges.2.2.2.2.1 hI hIrel hT
end Oberwolfach
