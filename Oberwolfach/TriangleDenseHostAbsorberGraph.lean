module

public import Oberwolfach.TriangleDenseHostAbsorber
public import Oberwolfach.OrdinaryAbsorberGraphRealization
public import Oberwolfach.TriangleDiagramGeometry

@[expose] public section
/-! Construct the finite diagram and its triangle absorber directly from
minimum degree and near-complete spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_dense_host_absorber_graph (β:ℝ) (hβ:0<β):
  ∃ ε₀:ℝ,0<ε₀ ∧ ∀ m f:ℕ,∃ N₀ K₀:ℕ,
  ∀ (V₀ U₀ V U:Type) [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→K₀≤Fintype.card U→Fintype.card V₀+Fintype.card U₀≤m→
  ∀ (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (Q:SimpleGraph V) (H:V→U→Prop)
    (W:Finset V) (B₀:Finset U) (φ:V₀↪V) (ψ:U₀↪U),
    (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀ u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))→
    (∀ v u,Hs v u→H (φ v) (ψ u))→(∀ u,ψ u∈B₀)→
    W.card≤f→B₀.card≤f→
    (∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))→
  ∀ ε:ℝ,0≤ε→ε≤ε₀→
    (∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))→
    (∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))→
  ∃ (R:SimpleGraph V) (K:V→U→Prop),
    R≤Q ∧ (∀ v u,K v u→H v u) ∧ Disjoint R (G.map φ) ∧
    (∀ v u,¬(K v u∧ordinaryMappedSpokes Hs φ ψ v u)) ∧
    (ordinaryPhysicalGraph R K).support.toFinset.card≤2*(5*ordinaryDiagramSize 3 m+2*(max f m)+4*K₀) ∧
    (∀ v∈(Finset.univ.image φ)∪W,∀ w∈(Finset.univ.image φ)∪W,¬R.Adj v w) ∧
    (∀ v∈(Finset.univ.image φ)∪W,∀ u∈B₀,¬K v u) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3)) (ordinaryHostResources R K) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=⊥) (Hbase:=H) (r:=3))
      (ordinaryHostResources (R⊔G.map φ) (fun v u=>K v u∨ordinaryMappedSpokes Hs φ ψ v u)) :=by
  obtain ⟨ε₀,hε₀,habs⟩:=triangle_dense_host_absorber β hβ
  refine ⟨ε₀,hε₀,?_⟩
  intro m f
  obtain ⟨N₀,K₀,habs⟩:=habs m f
  refine ⟨N₀,K₀,?_⟩
  intro V₀ U₀ V U _ _ _ _ _ _ _ _ hn hU hm G Hs Q H W B₀ φ ψ hbal hdiv hG hHs hψ hW hB hdeg ε hε hεsmall hnearV hnearU
  obtain ⟨C,hC,hhost,hrows,hhubs,havoid⟩:=habs V₀ U₀ V U hn hU hm G Hs Q H W B₀ φ ψ
    hbal hdiv hG hHs hψ hW hB hdeg ε hε hεsmall hnearV hnearU
  let b:=5*ordinaryDiagramSize 3 m+2*(max f m)+4*K₀
  let R:=ordinaryResourceRim Q C
  let K:V→U→Prop:=fun v u=>Sum.inr (v,u)∈C
  have hh:=ordinary_absorber_graph_realization Q ⊥ (G.map φ) H (ordinaryMappedSpokes Hs φ ψ) 3 C hhost hC b b hrows hhubs
    ((Finset.univ.image φ)∪W) B₀ havoid
  refine ⟨R,K,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.2⟩
  simpa only [b, two_mul] using hh.2.2.2.2.1
end Oberwolfach
