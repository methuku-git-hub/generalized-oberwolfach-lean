module

public import Oberwolfach.OrdinaryTransformerEdgePaths
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

 structure OrdinaryTransformerEdgeData (G Q F:SimpleGraph V) (H₀ H:V→U→Prop)
    (φ:V→V) (ψ:U→U) (r:ℕ) (A R W:Finset V) (B:Finset U) where
  b : ∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2)
  σ : ∀ v,Equiv.Perm (G.neighborSet v)
  shifted : ∀ v w,σ v w≠w
  path : (G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c)
  isPath : ∀ i,(path i).2.2.IsPath
  positive : ∀ i,0<(path i).2.2.length
  spoke_length : ∀ i:{e:V×U // H₀ e.1 e.2},(path (.inr i)).2.2.length=r-2
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
  buffer_card : buffer.card≤W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1)
  rim : OrdinaryActualRimWheels G Q F H₀ H φ r B b σ path
  spoke : OrdinaryActualSpokeWheels G Q F H₀ H φ ψ r path

 theorem ordinary_transformer_edge_realization
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (r:ℕ) (hr:4≤r) (A R W:Finset V) (B:Finset U)
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
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hspoke:∀ i:{e:V×U // H₀ e.1 e.2},∀ v w,
      c≤(((A.filter (fun a=>H a i.val.2∧H a (ψ i.val.2)))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hthree:r=4→∀ v w x,c≤(((A∩Q.neighborFinset v)∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1:ℕ)+r+7)*(d+1)<c)
    (hhubs:∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common (Finset.univ:Finset U) T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hhbudget:B.card+G.edgeFinset.card<cH):
    Nonempty (OrdinaryTransformerEdgeData G Q F H₀ H φ ψ r A R W B):=by
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
  obtain ⟨p,hp,hep,hsp,hsep⟩:=ordinary_transformer_edge_paths Q F H A W R
    (fun i:G.edgeFinset=>i.val.out.1) (fun i=>i.val.out.2) (fun i=>φ i.val.out.1) (fun i=>φ i.val.out.2)
    (fun i:{e:V×U // H₀ e.1 e.2}=>i.val.1) (fun i=>φ i.val.1) (fun i=>i.val.2) (fun i=>ψ i.val.2)
    heRoots hspRoot (fun i=>hFroots _ _ (edge_out_adj G i)) hspF r hr d c hd hF hcount hspoke
    (fun hr4 i v _=>hthree hr4 v i.val.out.2 (φ i.val.out.2))
    (by simpa only [Fintype.card_coe] using hbudget)
  have hFF:∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w:=by
    intro i j
    by_cases hij:i=j
    · subst j;exact (hp i).2.2
    · exact (hsep i j hij).2
  have hFR:∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w:=fun i v hv=>(hp i).2.1 v hv |>.2.2.2
  have hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset:=fun i j hij=>(hsep i j hij).1
  obtain ⟨E⟩:=ordinary_actual_rim_wheels G Q F H₀ H φ b σ p r (by omega) R B hroot hQ hφQ hcross hφedge
    (fun i=>⟨(hp _).1,(hep i).1⟩) (fun i=>(hep i).2) (fun i v hv=>(hp i).2.1 v hv |>.2.2.1)
    hdis hFF hFR (fun i=>hFroots _ _ (edge_out_adj G i)) cH hhubs hhbudget
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
  obtain ⟨S⟩:=ordinary_actual_spoke_wheels G Q F H₀ H φ ψ r (by omega) p R
    (fun i=>⟨(hspRoot i).1,(hspRoot i).2,(hcross _ (balanced_spoke_root_mem_support G H₀ hbalance i)
      _ (balanced_spoke_root_mem_support G H₀ hbalance i)).symm⟩)
    (fun i=>⟨(hp _).1,(hsp i).1⟩) (fun i=>⟨(hsp i).2.1,(hsp i).2.2.1,(hsp i).2.2.2.1,(hsp i).2.2.2.2.1⟩)
    (fun i v hv=>(hp i).2.1 v hv |>.2.2.1) hdis hFsp
    (fun i=>hH _ _ i.property) (fun i=>(hsp i).2.2.2.2.2) hψedge
  let W':=W∪Finset.univ.biUnion (fun i=>(p i).2.2.support.toFinset)
  have hcard (i):(p i).2.2.support.toFinset.card≤r-1:=by
    have hh:=List.toFinset_card_le (p i).2.2.support
    rw [(p i).2.2.length_support] at hh
    rcases i with i|i
    · rw [(hep i).1] at hh;omega
    · rw [(hsp i).1] at hh;omega
  have hW'card:W'.card≤W.card+(G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1):=by
    have hc:=Finset.card_biUnion_le (s:=(Finset.univ:Finset (G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})))
      (t:=fun i=>(p i).2.2.support.toFinset)
    have hc':(∑ i,(p i).2.2.support.toFinset.card)≤
        (G.edgeFinset.card+Fintype.card {e:V×U // H₀ e.1 e.2})*(r-1):=by
      calc
        _≤∑ _i:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2}),(r-1):=Finset.sum_le_sum (fun i _=>hcard i)
        _= _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_coe,Nat.cast_id]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (hc.trans hc') _)
  refine ⟨⟨b,σ,hσ,p,fun i=>(hp i).1,?_,fun i=>(hsp i).1,
    (fun i v hv=>⟨((hp i).2.1 v hv).1,((hp i).2.1 v hv).2.1,((hp i).2.1 v hv).2.2.1⟩),hdis,hFF,hFR,
    (fun i=>(hep i).2),(fun i=>⟨(hsp i).2.1,(hsp i).2.2.1,(hsp i).2.2.2.1,(hsp i).2.2.2.2.1⟩),
    (fun i=>(hsp i).2.2.2.2.2),W',Finset.subset_union_left,?_,hW'card,E,S⟩⟩
  · intro i;rcases i with i|i
    · rw [(hep i).1];omega
    · rw [(hsp i).1];omega
  · intro i v hv
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩)

end Oberwolfach
