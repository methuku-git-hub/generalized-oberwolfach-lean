module

public import Oberwolfach.OrdinaryRelativeHostAbsorber
public import Oberwolfach.OrdinaryActiveRootImages

@[expose] public section

/-! Apply the constructed absorber to an actual bounded physical remainder.
The finite root types are its active rows and hubs, so no isolated ambient
labels contribute to the order or forbidden-vertex conclusions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem ordinary_relative_ambient_absorber (r:ℕ) (hr:3≤r)
    (Tpls:Tpl→VertexAbsorberTemplate r) (β a b B:ℝ)
    (hβ:0<β) (ha:0<a) (hb:0<b) (hB:0<B) :
    ∃ η ε:ℝ,0<η∧0<ε∧ε≤β/4∧∀ m:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∀ d:ℝ,0≤d→∃ n₀:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      n₀≤Fintype.card V→
      ∀ (G:SimpleGraph V) (Hs:V→U→Prop) (Q F:SimpleGraph V) (H:V→U→Prop)
      (A Z W:Finset V) (B₀:Finset U),
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m→
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      G≤Q→(∀ v u,Hs v u→H v u)→
      (∀ u,(∃ v,Hs v u)→u∈B₀)→(∀ v w,Q.Adj v w→¬F.Adj v w)→
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
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C∧
        C⊆ordinaryHostResources Q H∧(ordinaryResourceRows C).card≤a₀∧(ordinaryResourceHubs C).card≤b₀∧
        ordinaryResourceRows C⊆G.support.toFinset∪A∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈G.support.toFinset)∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.filter (fun u=>∃ v,Hs v u))∧
        Disjoint C (ordinaryRootResources W B₀) := by
  obtain ⟨η,ε,hη,hε,hεβ,hbase⟩:=ordinary_relative_host_absorber r hr Tpls β a b B hβ ha hb hB
  refine ⟨η,ε,hη,hε,hεβ,?_⟩
  intro m
  obtain ⟨a₀,b₀,hbase⟩:=hbase m
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨n₀,hbase⟩:=hbase f d hd
  refine ⟨n₀,?_⟩
  intro V U _ _ _ _ hn G Hs Q F H A Z W B₀ hm hbal hdiv hG hHs hB₀old hQF hA hZ hW hB₀ hF hcount hpair hthree hfour hspfour hhub P
  have hsmall: Fintype.card (OrdinaryActiveRow G)+Fintype.card (OrdinaryActiveHub Hs)≤m:=
    (ordinary_active_root_order G Hs).trans hm
  have hdv:=ordinarySupport_balance_divisibility G Hs r hbal hdiv
  have result:=hbase (OrdinaryActiveRow G) (OrdinaryActiveHub Hs) V U hn hsmall
    (ordinarySupportRim G) (ordinarySupportSpokes G Hs) Q F H A Z W B₀
    (ordinaryActiveRowEmbedding G) (ordinaryActiveHubEmbedding Hs)
    (by intro v;simpa only [←SimpleGraph.ncard_neighborSet] using hdv.1 v) hdv.2
    (fun v w h=>hG h) (fun v u h=>hHs v.val u.val h)
    (fun u=>hB₀old u.val u.property) hQF hA hZ hW hB₀ hF hcount hpair hthree hfour hspfour hhub P
  simpa only [ordinarySupportRim_map,ordinarySupportSpokes_map G Hs hbal,
    ordinaryActiveRow_image,ordinaryActiveHub_image] using result

end Oberwolfach
