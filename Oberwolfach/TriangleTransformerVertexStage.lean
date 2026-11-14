module

public import Oberwolfach.TriangleActualVertexWheels
public import Oberwolfach.OrdinaryTransformerEdgeStage
public import Oberwolfach.TransformerSpokeDefectIdentity
public import Oberwolfach.TransformerOriginalEdgeIdentity

@[expose] public section

/-! Construct, rather than assume, the complete vertex-wheel stage over
already selected rim/spoke paths and their edge-wheel pairs. The result
is two actual decompositions with precisely the remaining hub-switch defect. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem triangular_transformer_vertex_stage_realization
    (G Q F:SimpleGraph V) (H₀ H:V→U→Prop) (φ:V→V) (ψ:U→U)
    (b:∀ v,G.neighborSet v≃({u:U // H₀ v u}×Fin 2))
    (σ:∀ v,Equiv.Perm (G.neighborSet v)) (hσ:∀ v w,σ v w≠w)
    (p:(G.edgeFinset⊕{e:V×U // H₀ e.1 e.2})→(Σ a:V,Σ c:V,Q.Walk a c))
    (R W:Finset V) (B:Finset U) (hRW:R⊆W)
    (hbalance:∀ v,G.degree v=2*((Finset.univ:Finset U).filter (H₀ v)).card)
    (hroot:∀ v∈G.support,v∈R∧φ v∈R)
    (hcross:∀ v∈G.support,∀ w∈G.support,φ v≠w)
    (hφQ:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w))
    (hφedge:Function.Injective (fun i:G.edgeFinset=>s(φ i.val.out.1,φ i.val.out.2)))
    (hψedge:Function.Injective (fun i:{e:V×U // H₀ e.1 e.2}=>(φ i.val.1,ψ i.val.2)))
    (hB:∀ e:{e:V×U // H₀ e.1 e.2},e.val.2∈B∧ψ e.val.2∈B)
    (hrim:∀ e:G.edgeFinset,(p (.inl e)).2.2.length=0)
    (hsp:∀ e:{e:V×U // H₀ e.1 e.2},(p (.inr e)).2.2.IsPath∧0<(p (.inr e)).2.2.length)
    (hpW:∀ i,∀ v∈(p i).2.2.support,v∈W∧v∉R)
    (hdis:∀ i j,i≠j→Disjoint (p i).2.2.support.toFinset (p j).2.2.support.toFinset)
    (hFF:∀ i j,∀ v∈(p i).2.2.support,∀ w∈(p j).2.2.support,¬F.Adj v w)
    (hFR:∀ i,∀ v∈(p i).2.2.support,∀ w∈R,¬F.Adj v w)
    (hends:∀ e:G.edgeFinset,Q.Adj e.val.out.1 (p (.inl e)).1 ∧
      Q.Adj (φ e.val.out.1) (p (.inl e)).1 ∧ Q.Adj e.val.out.2 (p (.inl e)).2.1 ∧
      Q.Adj (φ e.val.out.2) (p (.inl e)).2.1)
    (hspends:∀ e:{e:V×U // H₀ e.1 e.2},Q.Adj e.val.1 (p (.inr e)).1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).1 ∧ Q.Adj e.val.1 (p (.inr e)).2.1 ∧
      Q.Adj (φ e.val.1) (p (.inr e)).2.1)
    (hab:∀ d:Σ v,G.neighborSet v,Q.Adj
      (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d))
    (E:OrdinaryActualRimWheels G Q F H₀ H φ 3 B b σ p)
    (S:OrdinaryActualSpokeWheels G Q F H₀ H φ ψ 3 p):
    ∃ D:∀ d:Σ v,G.neighborSet v,
      OrdinaryVertexWheelPair Q F H 3 d.1 (φ d.1)
        (transformerRimEndpoint G Q H₀ p d) (transformerSpokeEndpoint G Q H₀ b p d)
        (transformerAssignedHub G σ E.hub d),
    let Plus:=Sum.elim E.first (Sum.elim S.first (fun d=>(D d).second))
    let Minus:=Sum.elim E.second (Sum.elim S.second (fun d=>(D d).first))
    let Z:U→Finset V:=fun u=>(Finset.univ.filter (fun i:{e:V×U // H₀ e.1 e.2}=>i.val.2=u)).biUnion
      (fun i=>(p (.inr i)).2.2.support.toFinset)
    (∀ d,∀ v∈rootWheelInternal (D d).first d.1 (transformerRimEndpoint G Q H₀ p d)
        (transformerSpokeEndpoint G Q H₀ b p d),False) ∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Plus i)) (ordinaryWheelResources (Plus j))) ∧
    (∀ i j,i≠j→Disjoint (ordinaryWheelResources (Minus i)) (ordinaryWheelResources (Minus j))) ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Plus) (wheelFamilySpokes Plus) 3 ∧
    HasOrdinaryWheelDecomposition (wheelFamilyRim Minus) (wheelFamilySpokes Minus) 3 ∧
    ∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources (wheelFamilyRim Plus) (wheelFamilySpokes Plus) then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources (wheelFamilyRim Minus) (wheelFamilySpokes Minus) then 1 else 0)=
      (if e∈ordinaryHostResources G H₀ then 1 else 0)-
      (if e∈transformerImageResources G H₀ φ ψ then 1 else 0)+
      ∑ u:U,((if e∈(Z u).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈(Z u).image (fun v=>Sum.inr (v,ψ u)) then 1 else 0)):=by
  have hrd (d:Σ v,G.neighborSet v):d.1∈R∧φ d.1∈R∧d.1≠φ d.1:=by
    have hd:G.Adj d.1 d.2.val:=d.2.property
    have hs:=hd.mem_support_left
    exact ⟨(hroot _ hs).1,(hroot _ hs).2,(hcross _ hs _ hs).symm⟩
  obtain ⟨D,hD,hd₁,hd₂,_,_⟩:=triangular_actual_vertex_wheels G Q F H₀ H φ b σ hσ E.hub p R W
    hrd (fun v w hvw=>(hφQ v w hvw).ne) hrim hsp hpW hdis hFF hFR hends hspends
    E.root_hub_adjacency E.attachments hab
  have hh:=ordinary_transformer_edge_stage G Q F H₀ H φ ψ 3 (by omega) R W B hRW b σ hσ p
    hbalance hroot hcross hB hpW hdis E S D (fun d v hv=>(hD d v hv).elim) hd₁ hd₂
  dsimp only at hh
  refine ⟨D,hD,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
  intro e
  rw [hh.2.2.2.2 e,transformer_original_edge_identity G H₀ φ ψ hφedge hψedge]
  rw [transformer_spoke_defect_identity Q H₀ ψ (fun i=>p (.inr i))
    (fun i j hij=>hdis (.inr i) (.inr j) (fun he=>hij (Sum.inr.inj he)))]

end Oberwolfach
