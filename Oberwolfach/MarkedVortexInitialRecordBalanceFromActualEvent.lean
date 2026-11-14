module

public import Oberwolfach.MarkedVortexInitialBalanceTransferFromActualEvent

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

theorem marked_vortex_initial_record_balance_from_actual_event
    (r:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d L:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
      (τ:RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (epsBal ζbal:ℝ),
    0≤epsBal→0≤ζbal→epsBal+((r+4)+2:ℕ)*ζbal≤etaBal/2→
    epsBal+((r+4)+2:ℕ)*ζbal≤x/4→L+1=Q.length→
    MarkedActualVortexBalanceProperty Q π hπ d (r+4) L a j epsBal ζbal
      (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z→
    (L=0 ∨ MarkedActualVortexBalanceProperty Q π hπ d (r+4) (L-1) a j epsBal ζbal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z)→
    let σ:=z.1
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
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
    ∃errI errT:ℝ,0≤errT ∧ errI≤(x/2)*Fintype.card W ∧ errT≤(x/2)*Fintype.card W ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) T R v j|≤errT) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤etaBal*I.card) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_vortex_initial_balance_transfer_from_actual_event r etaBal x iota hη hx hi
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ G D m β ε Q π hπ d L a j z τ H' FR FS epsBal ζbal
    heps hbal hrelative hambient hterminal hI hT σ H hinterval hR hS hFR hFS hH hH'
    W Z f g ρ σ₀ τ₀ H₀ H₀' I J T R E K S E' K' S' hsize
  obtain ⟨errI,errT,hi,ht,hiX,htX,hiRel,hIbal,hTbal⟩:=
    htransfer ζ hζ hζcap V U Γ Color G D m β ε Q π hπ d L a j z τ H' FR FS epsBal ζbal
      heps hbal hrelative hambient hterminal hI hT hinterval hR hS hFR hFS hH hH' hsize
  exact ⟨errI,errT,ht,hiX,htX,hIbal,hTbal,fun v j=>(hIbal v j).trans hiRel⟩
end Oberwolfach
