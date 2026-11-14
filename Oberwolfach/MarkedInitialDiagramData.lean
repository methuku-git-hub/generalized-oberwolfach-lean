module

public import Oberwolfach.MarkedVertexWheelConstruction
public import Oberwolfach.MarkedConstructedFamilyPacking
public import Oberwolfach.MarkedPathUnionGeometry

@[expose] public section

/-! The concrete data shared by the construction, integer identity, and
hub-switch callers. Every field refers to an actual path, wheel, incidence
assignment or physical packing. A later theorem constructs this record
from host counts; the record is not a main-theorem assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure MarkedInitialDiagram {V U E K A S:Type}
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b l:ℕ)
    (src dst:A→V) (row:S→V) (φ:V→V) (u u':S→U) (jr:A→Bool) (js:S→Bool)
    (W Z:Finset V) (B:Finset U) where
  a:∀ v,{e:A // dst e=v}≃{s:S // row s=v}
  d:∀ v,{e:A // src e=v}≃{s:S // row s=v}
  τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)
  deranged:∀ v z,τ v z≠z
  incomingType:∀ v e,js (a v e).val=markedIncidenceSpokeType jr (τ v (Sum.inl e))
  outgoingType:∀ v e,markedIncidenceSpokeType jr (τ v (Sum.inr e))=false
  pr:A→(Fin (l+3)↪V)
  ps:S→(Fin (l+4)↪V)
  pv:(Σ v,DirectedIncidence src dst v)→(Fin (l+4)↪V)
  hub:A↪U
  freshHub:∀ e,hub e∉B
  RC:A→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  RD:A→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  SC:S→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  SD:S→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  VC:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  VD:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK
  rimCoordinates:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e))
    (canonicalMarkedRotation (if jr e then 0 else 3) i)
  imageRimCoordinates:∀ e i,(RD e).1.val i=Fin.cons (α:=fun _=>V) (φ (src e)) (Fin.cons (φ (dst e)) (pr e))
    (canonicalMarkedRotation (if jr e then 0 else 3) i)
  rimHubs:∀ e,(RC e).2.val=hub e∧(RD e).2.val=hub e
  spokeCoordinates:∀ s i,(SC s).1.val i=rootedCycleOrder (markedRootOrder (l+4) (js s)) (row s) (ps s) i
  imageSpokeCoordinates:∀ s i,(SD s).1.val i=rootedCycleOrder (markedRootOrder (l+4) (js s)) (φ (row s)) (ps s) i
  spokeHubs:∀ s,(SC s).2.val=u s∧(SD s).2.val=u' s
  vertexCoordinates:∀ z i,(VC z).1.val i=rootedCycleOrder (markedRootOrder (l+4)
    (markedIncidenceSpokeType jr (τ z.1 z.2))) z.1 (pv z) i
  imageVertexCoordinates:∀ z i,(VD z).1.val i=rootedCycleOrder (markedRootOrder (l+4)
    (markedIncidenceSpokeType jr (τ z.1 z.2))) (φ z.1) (pv z) i
  vertexHubs:∀ z,(VC z).2.val=hub (directedIncidenceEdge (τ z.1 z.2))∧
    (VD z).2.val=hub (directedIncidenceEdge (τ z.1 z.2))
  vertexEnds:∀ z,pv z 0=markedAttachmentFirst (l+2) a d (fun e=>pr e) (fun s=>ps s) z∧
    pv z (Fin.last (l+3))=markedAttachmentLast (l+2) a d (fun e=>pr e) (fun s=>ps s) z
  rimAvoid:∀ e k,pr e k∉W∧pr e k∉Z∧∀ z∈Z,¬PermutationClose π b (pr e k) z
  spokeAvoid:∀ s k,ps s k∉W∧ps s k∉Z∧∀ z∈Z,¬PermutationClose π b (ps s k) z
  vertexAvoid:∀ z k,pv z k∉Z∧∀ y∈Z,¬PermutationClose π b (pv z k) y
  vertexNewAvoid:∀ z k,pv z k∈W∪markedPathUnion (l+3) (l+4) (fun e=>pr e) (fun s=>ps s)→
    pv z k∈({pv z 0,pv z (Fin.last (l+3))}:Finset V)
  rimDisjoint:∀ e e',e≠e'→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr e'))
  spokeDisjoint:∀ s s',s≠s'→Disjoint (Finset.univ.image (ps s)) (Finset.univ.image (ps s'))
  vertexDisjoint:∀ z z',z≠z'→Disjoint (Finset.univ.image (pv z)) (Finset.univ.image (pv z'))
  rimSpokeDisjoint:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s))
  pathSeparated:∀ x∈markedPathUnion (l+3) (l+4) (fun e=>pr e) (fun s=>ps s),
    ∀ y∈markedPathUnion (l+3) (l+4) (fun e=>pr e) (fun s=>ps s),x≠y→¬PermutationClose π b x y
  vertexSeparated:∀ z z' k k',pv z k≠pv z' k'→¬PermutationClose π b (pv z k) (pv z' k')
  vertexPathSeparated:∀ z k,∀ y∈markedPathUnion (l+3) (l+4) (fun e=>pr e) (fun s=>ps s),
    pv z k≠y→¬PermutationClose π b (pv z k) y
  plusPacking:∀ i j:A⊕(S⊕(Σ v,DirectedIncidence src dst v)),i≠j→
    Disjoint (markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) i))
      (markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) j))
  minusPacking:∀ i j:A⊕(S⊕(Σ v,DirectedIncidence src dst v)),i≠j→
    Disjoint (markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) i))
      (markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) j))

end Oberwolfach
