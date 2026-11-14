module

public import Oberwolfach.TriangleTransformerRootComplexity

@[expose] public section
/-! Express the triangle transformer's uniform constants in terms of
bounded root vertex sets rather than separate edge and incidence bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_transformer_uniform_bounded_vertices
    (β:ℝ) (hβ:0<β) (hβ1:β≤1):
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
  obtain ⟨ε₀,hε₀,huniform⟩:=triangle_transformer_uniform_bounded_inputs β hβ hβ1
  refine ⟨ε₀,hε₀,?_⟩
  intro q
  let c:=2*q*q+3*q+1
  obtain ⟨s₀,hs⟩:=huniform c
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨N₀,M₀,hbase⟩:=hs s hs₀ hsdiv
  refine ⟨N₀,M₀,?_⟩
  intro V U _ _ _ _ hn hm G Q H₀ H φ ψ R W R₀ B B₀ hRW hbalance hdiv hroot hcross hu hQ hφQ hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hR₀ hB₀ hsupport hw hr hb
  obtain ⟨he,ht,hd⟩:=triangle_root_complexity_bound G H₀ R₀ B₀ q hbalance hsupport hR₀ hB₀
  have hw':W.card≤c:=by dsimp [c];omega
  have hr':R.card≤c:=by dsimp [c];omega
  have hb':B.card≤c:=by dsimp [c];omega
  have hc:q*q≤c:=by dsimp [c];nlinarith
  have hc2:2*(q*q)≤c:=by dsimp [c];nlinarith
  have he':G.edgeFinset.card≤c:=he.trans hc
  have ht':Fintype.card {e:V×U // H₀ e.1 e.2}≤c:=ht.trans hc
  have hd':Fintype.card (Σ v,G.neighborSet v)≤c:=hd.trans hc2
  simpa only [c] using hbase V U hn hm G Q H₀ H φ ψ R W B hRW hbalance hdiv hroot hcross hu hQ hφQ
    hφedge hψedge hH hB hdeg ε hε hεsmall hnearV hnearU hw' hr' hb' he' ht' hd'
end Oberwolfach
