module

public import Oberwolfach.TriangleDenseEdgeRealization
public import Oberwolfach.TriangleVertexStageCompletion
public import Oberwolfach.OrdinaryProfileTransformerCompletion

@[expose] public section
/-! Construct the triangle transformer from dense rim and near-complete
spoke graphs, with explicit finite root and forbidden-set budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_dense_transformer_from_explicit_budgets
    (K₀ L:ℕ) (β:ℝ) (hβ:0<β) (hβ1:β≤1):
    ∃ s₀:ℕ,∀ s:ℕ,s₀≤s→3∣s→∃ N₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N₀≤Fintype.card V→∀ (G Q:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hdiv:∀ u,3∣((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card)
    (hsize:∀ u,2*((Finset.univ:Finset V).filter (fun v=>H₀ v u)).card≤L)
    (hactive:Fintype.card {u:U // ∃v,H₀ v u}≤K₀)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hu:∀ u,(∃v,H₀ v u)→u≠ψ u)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hdeg:∀ v,(3/4+β)*(Fintype.card V:ℝ)≤(Q.degree v:ℝ))
    (ε:ℝ) (hε:0≤ε) (hεβ:ε≤β)
    (hnearV:∀ u,(((Finset.univ:Finset V).filter (fun v=>¬H v u)).card:ℝ)≤ε*(Fintype.card V:ℝ))
    (hnearU:∀ v,(((Finset.univ:Finset U).filter (fun u=>¬H v u)).card:ℝ)≤ε*(Fintype.card U:ℝ))
    (hbudgetEdge:((W.card+R.card+G.edgeFinset.card+2*Fintype.card {e:V×U // H₀ e.1 e.2}+1:ℕ):ℝ)
      <2*β*(Fintype.card V:ℝ))
    (hbudgetHub:((B.card+G.edgeFinset.card:ℕ):ℝ)<(1-9*ε)*(Fintype.card U:ℝ))
    (hbudgetStage:2*ε*(Fintype.card V:ℝ)+
      ((W.card+2*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})+
        6*Fintype.card (Σ v,G.neighborSet v):ℕ):ℝ)≤(β/4)*(Fintype.card V:ℝ)),
    ∃ W' N:Finset V,∃ T:Finset (Sym2 V⊕(V×U)),∃ B':Finset U,
      W⊆W' ∧ W'.card≤W.card+2*(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})+
        6*Fintype.card (Σ v,G.neighborSet v) ∧
      Disjoint N W' ∧ N.card≤K₀*s ∧
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
  obtain ⟨s₀,hs⟩:=triangle_vertex_wheels_and_hub_trades_complete K₀ L β hβ hβ1
  refine ⟨s₀,?_⟩
  intro s hs₀ hsdiv
  obtain ⟨N₀,hN₀⟩:=hs s hs₀ hsdiv
  refine ⟨N₀,?_⟩
  intro V U _ _ _ _ hn G Q H₀ H φ ψ R W B hRW hbalance hdiv hsize hactive hroot hcross hu hQ hφQ
    hφedge hψedge hH hB hdeg ε hε hεβ hnearV hnearU hbudgetEdge hbudgetHub hbudgetStage
  obtain ⟨D⟩:=triangle_transformer_dense_edge_realization G Q H₀ H φ ψ R W B β ε hβ hε hεβ
    hbalance hroot hcross hQ hφQ hφedge hψedge hH hdeg hnearV hnearU hbudgetEdge hbudgetHub
  have hbudget':2*ε*(Fintype.card V:ℝ)+
      ((D.buffer.card+6*Fintype.card (Σ v,G.neighborSet v):ℕ):ℝ)≤(β/4)*(Fintype.card V:ℝ):=by
    have hc:(D.buffer.card:ℝ)≤((W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*2:ℕ):ℝ):=by exact_mod_cast D.buffer_card
    push_cast at hc hbudgetStage ⊢
    linarith
  obtain ⟨W',N,T,hWW',hWcard,hNW,hNcard,hT,hRs,hSs,hRroot,hSroot,hRavoid,hSavoid,hHub,hHubAll⟩:=
    hN₀ V U hn G Q H₀ H φ ψ D.b D.σ D.shifted D.path R D.buffer B (hRW.trans D.contains_old)
      hbalance hdiv hsize hactive hroot hcross hu hφQ hφedge hψedge hB D.rim_length
      (fun i=>⟨D.isPath _,D.spoke_length i⟩)
      (fun i v hv=>⟨D.contains_paths i v hv,(D.path_location i v hv).2.2⟩)
      W D.contains_old (fun i v hv=>(D.path_location i v hv).2.1) D.path_disjoint
      D.rim_ends D.spoke_ends D.endpoint_adjacent D.rim D.spoke hdeg ε hnearV hbudget'
  have hTS:T⊆ordinaryHostResources Q H:=
    Finset.subset_union_left.trans (ordinary_host_decomposition_subhost _ hT.2.2.1)
  let I:Type:={u:U // ∃v,H₀ v u}
  let B':Finset U:=(Finset.univ.image D.rim.hub)∪(Finset.univ.image (fun i:I=>i.val))∪
      (Finset.univ.image (fun i:I=>ψ i.val))
  have hBcard:B'.card≤G.edgeFinset.card+2*Fintype.card I:=by
    have h₁:=Finset.card_union_le (Finset.univ.image D.rim.hub) (Finset.univ.image (fun i:I=>i.val))
    have h₂:=Finset.card_union_le ((Finset.univ.image D.rim.hub)∪(Finset.univ.image (fun i:I=>i.val)))
      (Finset.univ.image (fun i:I=>ψ i.val))
    have hE:(Finset.univ.image D.rim.hub).card≤G.edgeFinset.card:=by
      simpa only [Finset.card_univ,Fintype.card_coe] using (Finset.card_image_le (s:=(Finset.univ:Finset G.edgeFinset)) (f:=D.rim.hub))
    have hO:(Finset.univ.image (fun i:I=>i.val)).card≤Fintype.card I:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset I)) (f:=fun i:I=>i.val))
    have hI:(Finset.univ.image (fun i:I=>ψ i.val)).card≤Fintype.card I:=by simpa using (Finset.card_image_le (s:=(Finset.univ:Finset I)) (f:=fun i:I=>ψ i.val))
    dsimp only [B']
    omega
  have hBcover:∀ v z,Sum.inr (v,z)∈T→z∈B':=by
    intro v z he
    rcases hHubAll v z he with ⟨e,heq⟩|⟨u,hu,heq|heq⟩
    · exact heq ▸ Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩))
    · exact heq ▸ Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨u,hu⟩,Finset.mem_univ _,rfl⟩))
    · exact heq ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨u,hu⟩,Finset.mem_univ _,rfl⟩)
  refine ⟨W',N,T,B',D.contains_old.trans hWW',?_,hNW,hNcard,hT,hTS,hBcard,hBcover,hRs,hSs,hRroot,hSroot,hRavoid,hSavoid,hHub⟩
  have hc:=D.buffer_card
  omega
end Oberwolfach
