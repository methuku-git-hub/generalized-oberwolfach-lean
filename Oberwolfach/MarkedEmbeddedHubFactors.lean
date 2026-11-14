module

public import Oberwolfach.MarkedEmbeddedHubCycles
public import Oberwolfach.PhysicalEdgeGraphEmbedding
public import Oberwolfach.MarkedHubFactorOn

@[expose] public section

/-! An inner hub factor embeds as an actual ambient factor. Its physical
rim graph is exactly the graph image, so avoidance transfers by comap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U E K:Type} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]

theorem twistedTupleHead_embedding (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) {m:ℕ} (z:Fin (m+1)→W) (i:Fin (m+1)):
    twistedTupleHead π (f∘z) i=f (twistedTupleHead ρ z i):=by
  refine Fin.lastCases ?_ (fun i=>?_) i <;>
    simp only [twistedTupleHead,Fin.snoc_last,Fin.snoc_castSucc,Function.comp_apply,h]

theorem hubCycleEmbedding_physical_edges (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U)
    (C:HubMarkedCycle tail head ktail khead m ρ b H₀ HK u):
    hubCyclePhysicalEdges u (hubCycleEmbeddingEquiv f ρ π h tail head ktail khead m b H₀ HK u C)=
      (hubCyclePhysicalEdges u C).image (fun e=>e.image f):=by
  simp only [hubCyclePhysicalEdges,markedCyclePhysicalEdges,Finset.image_image,Function.comp_apply,
    markedCycle_physical_pair,hubCycleAsMarked]
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_apply,markedCycle_physical_pair]
  change {f (C.val i),twistedTupleHead π (f∘C.val) i}=({C.val i,twistedTupleHead ρ C.val i}:Finset W).image f
  rw [twistedTupleHead_embedding f ρ π h]
  simp only [Finset.image_insert,Finset.image_singleton]

def hubFactorEmbedding (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U) (Y:Finset W)
    (P:MarkedHubFactorOn tail head ktail khead m ρ b H₀ HK u Y):
    MarkedHubFactorOn (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
      (spokeRelationImage f H₀) (spokeRelationImage f HK) u (Y.image f) where
  cycles:=P.cycles.image (hubCycleEmbeddingEquiv f ρ π h tail head ktail khead m b H₀ HK u)
  disjoint:=by
    intro C hC D hD hCD
    obtain ⟨c,hc,hec⟩:=Finset.mem_image.mp hC
    obtain ⟨d,hd,hed⟩:=Finset.mem_image.mp hD
    subst C;subst D
    rw [hubCycleEmbedding_vertices,hubCycleEmbedding_vertices]
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨x,hx,hfx⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,hfy⟩:=Finset.mem_image.mp hv'
    have hxy:x=y:=f.injective (hfx.trans hfy.symm)
    exact Finset.disjoint_left.mp (P.disjoint c hc d hd (fun he=>hCD (congrArg _ he))) hx (hxy.symm ▸ hy)
  covers:=by
    rw [Finset.image_biUnion]
    simp_rw [hubCycleEmbedding_vertices]
    rw [←Finset.biUnion_image,P.covers]

theorem hubFactorEmbedding_rim (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U) (Y:Finset W)
    (P:MarkedHubFactorOn tail head ktail khead m ρ b H₀ HK u Y):
    (hubFactorEmbedding f ρ π h tail head ktail khead m b H₀ HK u Y P).rim=P.rim.map f:=by
  change physicalEdgeGraph ((P.cycles.image _).biUnion (hubCyclePhysicalEdges u))=P.rim.map f
  rw [Finset.image_biUnion]
  simp_rw [hubCycleEmbedding_physical_edges]
  rw [←Finset.biUnion_image,physicalEdgeGraph_image_map]
  rfl

theorem hubFactorEmbedding_avoids (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V)
    (h:∀ x,f (ρ x)=π (f x)) (tail head:E→W) (ktail khead:K→W)
    (m b:ℕ) (H₀ HK:W→U→Prop) (u:U) (Y:Finset W)
    (P:MarkedHubFactorOn tail head ktail khead m ρ b H₀ HK u Y) (F:SimpleGraph V)
    (hF:Disjoint P.rim (F.comap f)):
    Disjoint (hubFactorEmbedding f ρ π h tail head ktail khead m b H₀ HK u Y P).rim F:=by
  rw [hubFactorEmbedding_rim]
  exact graph_map_disjoint_of_comap P.rim F f hF

end Oberwolfach
