module

public import Oberwolfach.TriangleTransformerPositiveBeta
public import Oberwolfach.OrdinaryResourceEndpointSets

@[expose] public section
/-! Eliminate the auxiliary triangle factor size and give a single uniform
bound on both resource vertices and the order of the hub side. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_finite_resource_uniform
    (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ N₀ K₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→
    ∀ (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (R W R₀:Finset V) (B B₀:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hdiv:∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hu:∀ u,(∃v,H₀ v u)→u≠ψ u)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (ε:ℝ) (hε:0≤ε) (hεsmall:ε≤ε₀)
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (hR₀:R₀.card≤q) (hB₀:B₀.card≤q) (hsupport:∀ v u,H₀ v u→v∈R₀∧u∈B₀)
    (hw:W.card≤3*q) (hr:R.card≤3*q) (hb:B.card≤3*q),
    ∃ T:Finset (Sym2 V⊕(V×U)),
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) T ∧
      T⊆ordinaryHostResources Q H ∧
      (ordinaryResourceRows T).card+(ordinaryResourceHubs T).card≤K₀ ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈ordinaryResourceRows T,v∈W→v∈R) ∧
      (∀ z∈ordinaryResourceHubs T,z∈B→∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) :=by
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_transformer_positive_beta β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨s₀,hs⟩:=huniform q
  let t:=3*(s₀+1)
  have ht:s₀≤t:=by dsimp [t];omega
  have hdiv:3∣t:=by dsimp [t];exact dvd_mul_right 3 _
  obtain ⟨N₀,M₀,hbase⟩:=hs t ht hdiv
  let c:=2*q*q+3*q+1
  let K₀:=max M₀ (3*q+19*(q*q)+c*t)
  refine ⟨N₀,K₀,?_⟩
  intro V U _ _ _ _ hn hm G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdivRoot hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  have hm':M₀≤Fintype.card U:=(le_max_left _ _).trans hm
  obtain ⟨W',N,T,B',hWW,hWcard,hNW,hNcard,hT,hTS,hBcard,hBcover,hRs,hSs,hRroot,hSroot,hRavoid,hSavoid,hHub⟩:=
    hbase V U hn hm' G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdivRoot hroot hcross hu hQ hφQ
      hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  have hrows:ordinaryResourceRows T⊆W'∪N:=ordinaryResourceRows_subset T _ hRs hSs
  have hhubs:ordinaryResourceHubs T⊆B':=ordinaryResourceHubs_subset T B' hBcover
  have hcardR:(ordinaryResourceRows T).card≤W'.card+N.card:=
    (Finset.card_le_card hrows).trans (Finset.card_union_le _ _)
  have hcardU:(ordinaryResourceHubs T).card≤B'.card:=Finset.card_le_card hhubs
  obtain ⟨he,ht,hd⟩:=triangle_root_complexity_bound G H₀ R₀ B₀ q hbalance hsupport hR₀ hB₀
  have hactive:Fintype.card {u:U // ∃v,H₀ v u}≤q*q:=(triangle_active_hubs_le_spokes H₀).trans ht
  have hsize:(ordinaryResourceRows T).card+(ordinaryResourceHubs T).card≤3*q+19*(q*q)+c*t:=by
    dsimp [c] at hNcard ⊢
    nlinarith
  refine ⟨T,hT,hTS,hsize.trans (le_max_right _ _),hRroot,hSroot,?_,?_⟩
  · intro v hv hvW
    obtain ⟨e,he,hv⟩:=Finset.mem_biUnion.mp hv
    cases e with
    | inl e=>
      induction e using Sym2.ind with
      | _ a b=>
        have hv':v=a∨v=b:=by simpa using hv
        rcases hv' with h|h
        · subst v
          exact hRavoid a hvW b he
        · subst v
          exact hRavoid b hvW a (by simpa only [Sym2.eq_swap] using he)
    | inr e=>
      have hv':v=e.1:=by simpa using hv
      subst v
      exact hSavoid e.1 hvW e.2 he
  · intro z hz hzB
    obtain ⟨e,he,hz⟩:=Finset.mem_biUnion.mp hz
    cases e with
    | inl e=>simp at hz
    | inr e=>
      have hz':z=e.2:=by simpa using hz
      subst z
      exact hHub e.1 e.2 hzB he
end Oberwolfach
