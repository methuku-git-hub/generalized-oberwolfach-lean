module

public import Oberwolfach.OrdinaryDiagramAssemblyBounds
public import Oberwolfach.OrdinaryCommonCycleProfiles

@[expose] public section

/-! Construct the four transformers of a host diagram and finish the
absorber, with all size and exclusion conclusions. The only fractional input
is the fixed common-pair profile supplied before choosing the diagram. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_diagram_absorber (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB:0<B) :
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ M:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∀ d:ℝ,0≤d→∃ n₀:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→∀ (Q F:SimpleGraph V) (H:V→U→Prop)
      (A Z W R₀:Finset V) (B₀ O:Finset U) (original:Finset (Sym2 V⊕(V×U))),
      A=Finset.univ\Z→(Z.card:ℝ)≤ε*Fintype.card V→W.card≤f→(B₀.card:ℝ)≤ε*Fintype.card V+f→
      (∀ v,(F.degree v:ℝ)≤d)→
      (∀ v w,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (∀ u u' v w,β*Fintype.card V≤(((Finset.univ.filter (fun a=>H a u∧H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))→
      (r=4→∀ v w x,β*Fintype.card V≤((Q.neighborFinset v∩Q.neighborFinset w∩Q.neighborFinset x).card:ℝ))→
      (r=3→∀ w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (r=3→∀ u u' w x y z,β*Fintype.card V≤((Finset.univ.filter (fun a=>H a u∧H a u'∧Q.Adj w a∧Q.Adj x a∧Q.Adj y a∧Q.Adj z a)).card:ℝ))→
      (∀ T:Finset V,T.card≤r+6→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))→
      OrdinaryCommonCycleProfiles Q F H r Tpls β a b B η→
      OrdinaryHostDiagram r M Q F H original A W R₀ B₀ O→
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) original C∧
        C⊆ordinaryHostResources Q H∧(ordinaryResourceRows C).card≤a₀∧(ordinaryResourceHubs C).card≤b₀∧
        ordinaryResourceRows C⊆R₀∪A∧(∀ v∈ordinaryResourceRows C,v∈W→v∈R₀)∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈O)∧Disjoint C (ordinaryRootResources W B₀) := by
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_four_transformer_absorber r hr Tpls β a b B hβ ha hb hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro M
  obtain ⟨t,ht,hbase⟩:=hbase (5*M)
  refine ⟨5*M+4*(5*M*r*(t+5*(5*M))),5*M+4*(5*M*(5*M+2)),?_⟩
  intro f d hd
  obtain ⟨n₀,hbase⟩:=hbase (f+5*M) d hd
  refine ⟨n₀,?_⟩
  intro V U _ _ _ _ hn Q F H A Z W R₀ B₀ O original hA hZ hW hB₀ hF hcount hpair hthree hfour hspfour hhub P D
  let W':=W∪D.rows
  let B':=B₀∪D.hubs
  let L:=ordinaryRootResources D.rows B'
  have hW':W'.card≤f+5*M:=(Finset.card_union_le _ _).trans (Nat.add_le_add hW D.rows_card)
  have hB':(B'.card:ℝ)≤ε*Fintype.card V+(f+5*M:ℕ):=by
    have hh:(B'.card:ℝ)≤B₀.card+5*M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left D.hubs_card _)
    push_cast
    linarith only [hh,hB₀]
  have hne (j:Fin 4) (i:{u:U // ∃ v,(D.T j).K v u}):i.val≠(D.T j).ψ i.val:=
    (D.T j).disjointHubs _ i.property
  let w:∀ j:Fin 4,∀ i:{u:U // ∃ v,(D.T j).K v u},
      LocalOrdinaryCycle Q F (Finset.univ.filter (fun a=>H a i.val∧H a ((D.T j).ψ i.val))) r→ℝ:=
    fun j i=>P.weight _ _ (hne j i)
  have hfirst:finiteFiveAt D.D 0=original∪D.extra:=by simpa [finiteFiveAt] using D.first
  have hfinal:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (finiteFiveAt D.D 4):=by
    simpa [finiteFiveAt] using D.last_decomp
  have hD:∀ i,i≤4→finiteFiveAt D.D i⊆L:=by
    intro i hi
    rw [show finiteFiveAt D.D i=D.D ⟨i,by omega⟩ from finiteFiveAt_apply D.D ⟨i,by omega⟩]
    exact ordinaryRootResources_contains _ _ _ (D.Drows _) ((D.Dhubs _).trans Finset.subset_union_right)
  obtain ⟨K,hK,hKK,hKrows,hKhubs,habs⟩:=hbase V U hn (fun j=>(D.T j).G) Q F (fun j=>(D.T j).K) H
    (fun j=>(D.T j).φ) (fun j=>(D.T j).ψ) A Z D.rows W' B' L hA hZ
    ((ordinaryRootResources_rows _ _).trans Finset.subset_union_right) (ordinaryRootResources_hubs _ _)
    Finset.subset_union_right D.rows_card hW' hB'
    (fun j=>(D.T j).balance) (fun j=>(D.T j).div) (fun j=>(D.T j).column) (fun j=>(D.T j).hubs)
    (fun j=>(D.T j).roots) (fun j=>(D.T j).disjointRows) (fun j=>(D.T j).disjointHubs)
    (fun j=>(D.T j).sourceRim) (fun j=>(D.T j).targetRim) (fun j=>(D.T j).rimInj) (fun j=>(D.T j).spokeInj)
    (fun j=>(D.T j).hostSpokes) (fun j=>(D.T j).hubRoots) (fun j=>(D.T j).separation)
    hF hcount hpair hthree hfour hspfour hhub (fun j i=>P.size _ _ (hne j i)) w
    (fun j i=>P.bounds _ _ (hne j i)) (fun j i=>P.degree _ _ (hne j i)) (fun j i=>P.absorbers _ _ (hne j i))
    (finiteFiveAt D.D) original D.extra hfirst D.first_disjoint D.extra_decomp hfinal
    D.chain_endpoints D.chain_disjoint hD
  refine ⟨ordinaryDiagramAbsorberEdges D K,?_,?_⟩
  · simpa [ordinaryDiagramAbsorberEdges,finiteFiveAt] using habs
  · exact ordinary_diagram_assembly_bounds D K _ _ (fun j=>(hK j).2.1) (fun j=>(hK j).2.2.1)
      (fun j=>(hK j).2.2.2.1) (fun j=>(hK j).2.2.2.2.1) (fun j=>(hK j).2.2.2.2.2.2.2) hKrows hKhubs

end Oberwolfach
