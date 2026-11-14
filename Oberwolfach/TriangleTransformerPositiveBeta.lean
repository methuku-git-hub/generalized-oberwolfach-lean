module

public import Oberwolfach.TriangleTransformerBoundedVertices

@[expose] public section
/-! Remove the auxiliary upper bound on the degree margin. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_positive_beta
    (β:ℝ) (hβ:0<β):
    ∃ ε₀:ℝ,0<ε₀ ∧ ∀ q:ℕ,∃ s₀:ℕ,∀ s:ℕ,s₀≤s→3∣s→∃ N₀ M₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→M₀≤Fintype.card U→
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
    ∃ W' N:Finset V,∃ T:Finset (Sym2 V⊕(V×U)),∃ B':Finset U,
      W⊆W' ∧ W'.card≤W.card+2*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})+
        6*Fintype.card (Σ v,G.neighborSet v) ∧
      Disjoint N W' ∧ N.card≤(2*q*q+3*q+1)*s ∧
      IsResourceTransformer (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
        (ordinaryHostResources G H₀) (transformerImageResources G H₀ φ ψ) T ∧
      T⊆ordinaryHostResources Q H ∧
      B'.card≤G.edgeFinset.card+2*Fintype.card {u:U // ∃v,H₀ v u} ∧
      (∀ v z,Sum.inr (v,z)∈T→z∈B') ∧
      (∀ v w,Sum.inl s(v,w)∈T→v∈W'∪N∧w∈W'∪N) ∧
      (∀ v z,Sum.inr (v,z)∈T→v∈W'∪N) ∧
      (∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉T) ∧
      (∀ v∈R,∀ z∈B,Sum.inr (v,z)∉T) ∧
      (∀ v∈W,∀ w,Sum.inl s(v,w)∈T→v∈R) ∧
      (∀ v∈W,∀ z,Sum.inr (v,z)∈T→v∈R) ∧
      (∀ v z,z∈B→Sum.inr (v,z)∈T→∃ u,(∃x,H₀ x u) ∧ (z=u∨z=ψ u)) :=by
  let β':=min β 1
  have hb':0<β':=lt_min hβ (by norm_num)
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_transformer_uniform_bounded_vertices β' hb' (min_le_right _ _)
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  obtain ⟨s₀,hs⟩:=huniform q
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨N₀,M₀,hbase⟩:=hs s hs₀ hsdiv
  refine ⟨N₀,M₀,?_⟩
  intro V U _ _ _ _ hn hm G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  have hdeg':∀ v,(3/4+β')*(Fintype.card V:ℝ)≤(Q.degree v:ℝ):=by
    intro v
    have hn:0≤(Fintype.card V:ℝ):=by positivity
    have hb:β'≤β:=min_le_left _ _
    have hh:=mul_le_mul_of_nonneg_right hb hn
    have hv:=hdeg v
    nlinarith
  exact hbase V U hn hm G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdiv hroot hcross hu hQ hφQ
    hφedge hψedge hH hB hdeg' ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
end Oberwolfach
