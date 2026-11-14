module

public import Oberwolfach.MarkedRestrictedDegreePhysicalOnRoots
public import Oberwolfach.MarkedInnerDeepBalanceOrderedCaps
public import Oberwolfach.MarkedVortexInitialBalanceTransferFromActualEvent
public import Oberwolfach.MarkedVortexParentRecordSmallerReferenceEvent

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

theorem marked_vortex_initial_balance_from_parent_ambient_local_changes
    (r:ℕ) (x:ℝ) (hx:0<x):
    let cap:=Classical.choose (marked_inner_deep_balance_ordered_caps (r+4) x hx);
    0<cap ∧ ∀etaBal:ℝ,0<etaBal→∃c:ℝ,0<c ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d L:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
      (h k₀:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
      (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τLevel tolLocal ζLocal τParent tolParent ζParent ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
      (size a₀ b₀ e₀ f₀:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
      (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
      (τ:RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (epsBal ζbal:ℝ),
    0≤epsBal→0≤ζbal→epsBal+((r+4)+2:ℕ)*ζbal≤etaBal/2→
    epsBal+((r+4)+2:ℕ)*ζbal≤x/4→L+1=Q.length→
    MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τLevel tolLocal ζLocal τParent tolParent ζParent epsBal ζbal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hπ L s₀ p kval q s a j weightParent weight z→
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
    (∀mark v w,v∈I→w∈I→
      (markedPhysicalRim (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) mark v w=1))→
    (∀b v u,v∈I→u∈J→(H₀ b v u↔H₀' b v u))→
    (∀v,v∉Q.extendedVertices 1→(FR.degree v:ℝ)≤c*(I.card:ℝ))→
    (∀B:Finset U,∀v,v∉Q.extendedVertices 1→
      (∑u∈B,if ¬(H false v u↔H' false v u) then (1:ℝ) else 0)≤c*(I.card:ℝ))→
    (∀v u,H₀ true v u↔H₀' true v u)→
    (∀u v,v∈I→H₀' false v u→H₀ false v u)→
    (∀u,((I.filter (fun v=>H₀ false v u ∧ ¬H₀' false v u)).card:ℝ)≤c*(I.card:ℝ))→
    ∃errI errT:ℝ,0≤errT ∧ errI≤(x/2)*Fintype.card W ∧ errT≤(x/2)*Fintype.card W ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) T R v j|≤errT) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤etaBal*I.card) :=by
  intro cap
  have hcap:0<cap:=(Classical.choose_spec (marked_inner_deep_balance_ordered_caps (r+4) x hx)).1
  have hchoice:=(Classical.choose_spec (marked_inner_deep_balance_ordered_caps (r+4) x hx)).2
  refine ⟨hcap,?_⟩
  intro etaBal hη
  obtain ⟨c,hc,htransfer⟩:=hchoice etaBal hη
  refine ⟨c,hc,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ G D m β ε Q π hπ d L a j z h k₀ α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τLevel tolLocal ζLocal τParent tolParent ζParent ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ s₀ p kval q s weightParent weight τ H' FR FS epsBal ζbal
    heps hbal hrelative hambient hterminal hGood σ H hinterval hR hS hFR hFS hH hH'
    W Z f g ρ σ₀ τ₀ H₀ H₀' I J T R E K S E' K' S' hrim hspoke hFRoutside hrowAmbient hmark hnoNew hloss
  have hh:=hGood
  dsimp only [MarkedVortexParentRecordSmallerReferenceEvent] at hh
  obtain ⟨hI,hT,_⟩:=hh
  have hBounds:=marked_vortex_actual_initial_balance_with_slack Q π hπ d (r+4) L a j epsBal ζbal etaBal x
    heps hbal hrelative hambient hterminal z hI hT
  have hchanges:=marked_vortex_initial_sample_change_data Q π hπ d σ τ H H' FR FS ζ hinterval hR hS hFR hFS
  let Roots:Finset W:=Finset.univ\I
  have hRoots:∀v,v∈Roots→ρ v∈Roots:=by
    intro v hv
    have hvI:v∉I:=(Finset.mem_sdiff.mp hv).2
    have hπI:ρ v∈I↔v∈I:=(marked_vortex_permutation_compatibility Q π hπ 0).2.1 v
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h=>hvI (hπI.mp h)⟩
  have houtside:∀v:W,v∉I→f v∉Q.extendedVertices 1:=by
    intro v hv hmem
    apply hv
    change v∈markedVortexInnerVertices Q 0
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change v.val∈Q.extendedVertices 1
    simpa [f,markedVortexVertexEmbedding] using hmem
  have hFRlocal:∀v∈Roots,((FR.comap f).degree v:ℝ)≤c*(I.card:ℝ):=by
    intro v hv
    have hle:((FR.comap f).degree v:ℝ)≤FR.degree (f v):=by
      exact_mod_cast graph_comap_injective_degree_le FR f.toEmbedding v
    exact hle.trans (hFRoutside (f v) (houtside v (Finset.mem_sdiff.mp hv).2))
  have hRoutside:∀mark incoming v,v∉I→
      |(markedRestrictedDegree (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) mark incoming v I:ℝ)-
        (markedRestrictedDegree (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) mark incoming v I:ℝ)|≤c*(I.card:ℝ):=by
    intro mark incoming v hv
    have hh:=marked_restricted_degree_after_physical_changes_on_roots (G.comap f) ρ d I σ₀ τ₀ (FR.comap f)
      (c*(I.card:ℝ)) hchanges.2.1 Roots hRoots hFRlocal mark incoming v
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩)
    convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hrowOutside:∀v,v∉I→(∑u∈J,if ¬(H₀ false v u↔H₀' false v u) then (1:ℝ) else 0)≤c*(I.card:ℝ):=by
    intro v hv
    have hh:=hrowAmbient (J.image g) (f v) (houtside v hv)
    rw [Finset.sum_image (fun _ _ _ _ he=>g.injective he)] at hh
    convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hBounds
  try rw [hdec] at ⊢
  have hResult:=htransfer W Z Γ Color (G.comap f) ρ d I T J R ζ hζ hζcap σ₀ τ₀ H₀ H₀'
    (FR.comap f) (FS.comap (Sum.map f g))
    (by intro v u;exact hH (f v) (g u)) (by intro v u;exact hH' (f v) (g u))
    hchanges.2.1 hchanges.2.2.1 hchanges.2.2.2.1 hchanges.2.2.2.2.1
    hrim hspoke hRoutside hrowOutside hmark hnoNew hloss
    (by convert hBounds.1 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hBounds.2.1 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hBounds.2.2 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  dsimp only [S'] at hResult ⊢
  try rw [hdec] at ⊢
  exact hResult
end Oberwolfach
