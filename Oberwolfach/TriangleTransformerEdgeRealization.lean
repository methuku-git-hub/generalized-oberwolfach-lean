module

public import Oberwolfach.TriangleTransformerPaths
public import Oberwolfach.OrdinaryTransformerSpokeSets
public import Oberwolfach.OrdinaryActualRimWheels
public import Oberwolfach.OrdinaryActualSpokeWheels

@[expose] public section

/-! Realise the actual incidence choices, all rim/spoke paths, and their
edge-wheel pairs from graph-theoretic hypotheses. Paths are chosen before
fresh hubs, including the four shifted endpoint adjacencies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 512
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 structure TriangleTransformerEdgeData (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (A R W:Finset V) (B:Finset U) where
  b : ∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2)
  σ : ∀ v,Equiv.Perm (G.neighborSet v)
  shifted : ∀ v w,σ v w≠w
  path : (G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c)
  isPath : ∀ i,(path i).2.2.IsPath
  rim_length : ∀ i:G.edgeFinset,(path (.inl i)).2.2.length=0
  endpoint_adjacent : ∀ d:Σ v,G.neighborSet v,Q.Adj
    (transformerRimEndpoint G Q H₀ path d) (transformerSpokeEndpoint G Q H₀ b path d)
  spoke_length : ∀ i:{e:V×U // H₀ e.1 e.2},(path (.inr i)).2.2.length=1
  path_location : ∀ i,∀ v∈(path i).2.2.support,v∈A∧v∉W∧v∉R
  path_disjoint : ∀ i j,i≠j→Disjoint (path i).2.2.support.toFinset (path j).2.2.support.toFinset
  path_separated : ∀ i j,∀ v∈(path i).2.2.support,∀ w∈(path j).2.2.support,¬F.Adj v w
  root_separated : ∀ i,∀ v∈(path i).2.2.support,∀ w∈R,¬F.Adj v w
  rim_ends : ∀ e:G.edgeFinset,Q.Adj e.val.out.1 (path (.inl e)).1∧
    Q.Adj (φ e.val.out.1) (path (.inl e)).1∧Q.Adj e.val.out.2 (path (.inl e)).2.1∧
    Q.Adj (φ e.val.out.2) (path (.inl e)).2.1
  spoke_ends : ∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (path (.inr e)).1∧
    Q.Adj (φ e.val.1) (path (.inr e)).1∧Q.Adj e.val.1 (path (.inr e)).2.1∧
    Q.Adj (φ e.val.1) (path (.inr e)).2.1
  spoke_hubs : ∀ e:{e:V×U // H₀ e.1 e.2},∀ v∈(path (.inr e)).2.2.support,H v e.val.2∧H v (ψ e.val.2)
  buffer : Finset V
  contains_old : W⊆buffer
  contains_paths : ∀ i,∀ v∈(path i).2.2.support,v∈buffer
  buffer_card : buffer.card≤W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*2
  rim : OrdinaryActualRimWheels G Q F H₀ H φ 3 B b σ path
  spoke : OrdinaryActualSpokeWheels G Q F H₀ H φ ψ 3 path

 theorem triangular_transformer_edge_realization
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (A R W:Finset V) (B:Finset U)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hQ:G≤Q) (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun e:G.edgeFinset=>s(φ e.val.out.1,φ e.val.out.2)))
    (hψedge:Function.Injective (fun e:{e:V×U // H₀ e.1 e.2}=>(φ e.val.1,ψ e.val.2)))
    (hH:∀ v u,H₀ v u→H v u∧H (φ v) (ψ u))
    (hFroots:∀ v w,G.Adj v w→∀ a∈({v,w,φ v,φ w}:Finset V),
      ∀ c∈({v,w,φ v,φ w}:Finset V),¬F.Adj a c)
    (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hfour:∀ w x y z,c≤((A.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hspfour:∀ u u' w x y z,c≤((A.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+G.edgeFinset.card+2*Fintype.card {e:V×U // H₀ e.1 e.2}+1)*(d+1)<c)
    (hhubs:∀ T:Finset V,T.card≤9→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common (Finset.univ:Finset U) T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hhbudget:B.card+G.edgeFinset.card<cH):
    Nonempty (TriangleTransformerEdgeData G Q F H₀ H φ ψ A R W B):=by
  obtain ⟨σ,b,hσ,_⟩:=transformer_endpoint_assignments G H₀ hbalance
  have hspRoot (i:{e:V×U // H₀ e.1 e.2}):i.val.1∈R∧φ i.val.1∈R:=
    hroot _ (balanced_spoke_root_mem_support G H₀ hbalance i)
  have hspF (i:{e:V×U // H₀ e.1 e.2}):¬F.Adj i.val.1 (φ i.val.1):=by
    apply balanced_spoke_root_separation G F H₀ φ hbalance _ _ _ i.property
    intro v w hvw
    exact hFroots v w hvw v (by simp) (φ v) (by simp)
  have heRoots (i:G.edgeFinset):i.val.out.1∈R∧i.val.out.2∈R∧φ i.val.out.1∈R∧φ i.val.out.2∈R:=
    ⟨(hroot _ (edge_out_adj G i).mem_support_left).1,(hroot _ (edge_out_adj G i).mem_support_right).1,
      (hroot _ (edge_out_adj G i).mem_support_left).2,(hroot _ (edge_out_adj G i).mem_support_right).2⟩
  obtain ⟨p,hp,hrim,hsp,hclass,hdis,hFF,hends,hspends,hspH,hab⟩:=
    triangular_transformer_paths G Q F H₀ H φ ψ b A W R d c hd hF hfour hspfour hbudget
  have hFR:∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w:=fun i v hv=>(hclass i v hv).2.2.2
  obtain ⟨E⟩:=ordinary_actual_rim_wheels G Q F H₀ H φ b σ p 3 (by omega) R B hroot hQ hφQ hcross hφedge
    (fun i=>⟨hp _,hrim i⟩) hends (fun i v hv=>(hclass i v hv).2.2.1)
    hdis hFF hFR (fun i=>hFroots _ _ (edge_out_adj G i)) cH (by simpa using hhubs) hhbudget
  have hFsp (i:{e:V×U // H₀ e.1 e.2}):
      ∀ v∈insert i.val.1 (insert (φ i.val.1) (p (.inr i)).2.2.support.toFinset),
      ∀ w∈insert i.val.1 (insert (φ i.val.1) (p (.inr i)).2.2.support.toFinset),¬F.Adj v w:=by
    intro v hv w hw
    simp only [Finset.mem_insert,List.mem_toFinset] at hv hw
    rcases hv with rfl|rfl|hv <;> rcases hw with rfl|rfl|hw
    · exact F.loopless.irrefl _
    · exact hspF i
    · exact fun h=>hFR _ _ hw _ (hspRoot i).1 h.symm
    · exact fun h=>hspF i h.symm
    · exact F.loopless.irrefl _
    · exact fun h=>hFR _ _ hw _ (hspRoot i).2 h.symm
    · exact hFR _ _ hv _ (hspRoot i).1
    · exact hFR _ _ hv _ (hspRoot i).2
    · exact hFF _ _ _ hv _ hw
  obtain ⟨S⟩:=ordinary_actual_spoke_wheels G Q F H₀ H φ ψ 3 (by omega) p R
    (fun i=>⟨(hspRoot i).1,(hspRoot i).2,(hcross _ (balanced_spoke_root_mem_support G H₀ hbalance i)
      _ (balanced_spoke_root_mem_support G H₀ hbalance i)).symm⟩)
    (fun i=>⟨hp _,hsp i⟩) hspends
    (fun i v hv=>(hclass i v hv).2.2.1) hdis hFsp (fun i=>hH _ _ i.property) hspH hψedge
  let W':=W∪Finset.univ.biUnion (fun i=>(p i).2.2.support.toFinset)
  have hcard (i):(p i).2.2.support.toFinset.card≤2:=by
    have hh:=List.toFinset_card_le (p i).2.2.support
    rw [(p i).2.2.length_support] at hh
    rcases i with i|i
    · rw [hrim i] at hh;omega
    · rw [hsp i] at hh;omega
  have hW'card:W'.card≤W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*2:=by
    have hc:=Finset.card_biUnion_le (s:=(Finset.univ:Finset (G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})))
      (t:=fun i=>(p i).2.2.support.toFinset)
    have hc':(∑ i,(p i).2.2.support.toFinset.card)≤
        (G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*2:=by
      calc
        _≤∑ _i:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2}),(2:ℕ):=Finset.sum_le_sum (fun i _=>hcard i)
        _= _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_coe,Nat.cast_id]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (hc.trans hc') _)
  refine ⟨⟨b,σ,hσ,p,hp,hrim,hab,hsp,
    (fun i v hv=>⟨(hclass i v hv).1,(hclass i v hv).2.1,(hclass i v hv).2.2.1⟩),hdis,hFF,hFR,
    hends,hspends,hspH,W',Finset.subset_union_left,?_,hW'card,E,S⟩⟩
  intro i v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩)

end Oberwolfach
