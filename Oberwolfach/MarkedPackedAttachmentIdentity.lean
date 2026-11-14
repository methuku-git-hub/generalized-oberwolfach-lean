module

public import Oberwolfach.MarkedActualAttachmentIdentity
public import Oberwolfach.MarkedVertexPairIdentity
public import Oberwolfach.MarkedRimPairIdentity
public import Oberwolfach.MarkedAttachmentIdentity
public import Oberwolfach.ResourceFamilyIndicators
public import Oberwolfach.MarkedSpokeLoadGrouping
public import Oberwolfach.MarkedOldResourceIdentity

@[expose] public section

/-! Convert the actual packed attachment-wheel families to physical edge
sets. The original-edge contribution and the remaining free-spoke load
are identified exactly, including all multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 700000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype A] [Fintype S] [Fintype U] [DecidableEq A] [DecidableEq S] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_packed_attachment_identity (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (src dst:A→V) (row:S→V) (φ:V→V) (hub:A→U) (u u':S→U) (jr:A→Bool) (js:S→Bool)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (σ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (pr:A→Fin (n+1)→V) (ps:S→(Fin (n+2)↪V))
    (pv:(Σ v,DirectedIncidence src dst v)→Fin (n+2)→V)
    (jv:(Σ v,DirectedIncidence src dst v)→Bool)
    (RC RD:A→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (SC SD:S→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (VC VD:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hRC:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hRD:∀ e i,(RD e).1.val i=Fin.cons (α:=fun _=>V) (φ (src e)) (Fin.cons (φ (dst e)) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hRh:∀ e,(RC e).2.val=hub e∧(RD e).2.val=hub e)
    (hSC:∀ s i,(SC s).1.val i=rootedCycleOrder (markedRootOrder (n+2) (js s)) (row s) (ps s) i)
    (hSD:∀ s i,(SD s).1.val i=rootedCycleOrder (markedRootOrder (n+2) (js s)) (φ (row s)) (ps s) i)
    (hSh:∀ s,(SC s).2.val=u s∧(SD s).2.val=u' s)
    (hVC:∀ z i,(VC z).1.val i=rootedCycleOrder (markedRootOrder (n+2) (jv z)) z.1 (pv z) i)
    (hVD:∀ z i,(VD z).1.val i=rootedCycleOrder (markedRootOrder (n+2) (jv z)) (φ z.1) (pv z) i)
    (hVh:∀ z,(VC z).2.val=hub (directedIncidenceEdge (σ z.1 z.2))∧
      (VD z).2.val=hub (directedIncidenceEdge (σ z.1 z.2)))
    (hvin:∀ v e,jv ⟨v,Sum.inl e⟩=js (a v e).val∧
      pv ⟨v,Sum.inl e⟩ 0=pr e.val 0∧
      pv ⟨v,Sum.inl e⟩ (Fin.last (n+1))=ps (a v e).val (Fin.last (n+1)))
    (hvout:∀ v e,jv ⟨v,Sum.inr e⟩=false∧
      pv ⟨v,Sum.inr e⟩ 0=ps (d v e).val 0∧
      pv ⟨v,Sum.inr e⟩ (Fin.last (n+1))=pr e.val (Fin.last n))
    (ψ:U→U) (hu':∀ s,u' s=ψ (u s))
    (hps:∀ s t,s≠t→Disjoint (Finset.univ.image (ps s)) (Finset.univ.image (ps t)))
    (hr:Function.Injective (fun i=>if jr i then ({src i,π (dst i)}:Finset V) else {src i,dst i}))
    (hr':Function.Injective (fun i=>if jr i then ({φ (src i),π (φ (dst i))}:Finset V) else {φ (src i),φ (dst i)}))
    (hs:Function.Injective (fun s=>(row s,u s)))
    (hs':Function.Injective (fun s=>(φ (row s),u' s)))
    (hPlus:∀ i j:A⊕(S⊕(Σ v,DirectedIncidence src dst v)),i≠j→
      Disjoint (markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) i))
        (markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) j)))
    (hMinus:∀ i j:A⊕(S⊕(Σ v,DirectedIncidence src dst v)),i≠j→
      Disjoint (markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) i))
        (markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) j))):
    let P:=Finset.univ.biUnion (fun i:A⊕(S⊕(Σ v,DirectedIncidence src dst v))=>
      markedWheelPhysicalResources (Sum.elim RC (Sum.elim SC VD) i))
    let N:=Finset.univ.biUnion (fun i:A⊕(S⊕(Σ v,DirectedIncidence src dst v))=>
      markedWheelPhysicalResources (Sum.elim RD (Sum.elim SD VC) i))
    let L:=Finset.univ.image (fun i=>Sum.inl (if jr i then ({src i,π (dst i)}:Finset V) else {src i,dst i}))∪
      Finset.univ.image (fun s=>Sum.inr (row s,u s))
    let L':=Finset.univ.image (fun i=>Sum.inl (if jr i then ({φ (src i),π (φ (dst i))}:Finset V) else {φ (src i),φ (dst i)}))∪
      Finset.univ.image (fun s=>Sum.inr (φ (row s),u' s))
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=n+2) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=n+2) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
      ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
        (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
          ∑ z:U,((if e∈(spokePathHubVertices (n+2) ps u z).image (fun v=>Sum.inr (v,z)) then 1 else 0)-
            (if e∈(spokePathHubVertices (n+2) ps u z).image (fun v=>Sum.inr (v,ψ z)) then 1 else 0)):=by
  dsimp only
  refine ⟨resource_indexed_family_decomposition markedWheelPhysicalResources _ hPlus,
    resource_indexed_family_decomposition markedWheelPhysicalResources _ hMinus,?_⟩
  intro e
  have hP:=resource_indexed_family_int_indicator markedWheelPhysicalResources _ hPlus e
  have hN:=resource_indexed_family_int_indicator markedWheelPhysicalResources _ hMinus e
  rw [←hP,←hN]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  have ha:=marked_actual_attachment_integer_identity n hn hp src dst row φ hub u u' jr js a d σ
    pr (fun s=>ps s) pv jv RC RD SC SD VC VD hRC hRD hRh hSC hSD hSh hVC hVD hVh hvin hvout e
  have hold:=marked_old_resource_integer_identity _ _ _ _ hr hr' hs hs' e
  have hload:=marked_spoke_path_load_grouping (n+2) ps u ψ hps e
  rw [←hold]
  simp_rw [hu']
  rw [←hload]
  simp_rw [hu'] at ha
  simp only [Finset.sum_sub_distrib] at ha
  linear_combination ha

end Oberwolfach
