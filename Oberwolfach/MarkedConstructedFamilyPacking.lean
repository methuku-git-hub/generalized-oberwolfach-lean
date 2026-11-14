module

public import Oberwolfach.MarkedThreeFamilyPacking
public import Oberwolfach.MarkedVertexFamilyPacking
public import Oberwolfach.MarkedAttachmentEndpointOwnership

@[expose] public section

/-! Discharge all three within-family and all cross-family packing inputs
for the constructed wheels. A pair of row maps may identify old vertices;
only their arc endpoints and original physical edges must remain distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype A] [Fintype S]
  [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_constructed_family_packing (l:ℕ) (hl:1≤l)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (src dst:A→V) (row:S→V) (g f:V→V) (hub:A→U) (u:S→U)
    (jr:A→Bool) (js:S→Bool) (jv:(Σ v,DirectedIncidence src dst v)→Bool)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (hτ:∀ v i,τ v i≠i)
    (pr:A→(Fin (l+2)↪V)) (ps:S→(Fin (l+3)↪V))
    (pv:(Σ v,DirectedIncidence src dst v)→(Fin (l+3)↪V))
    (RC:A→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (SC:S→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (VC:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
    (hRC:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (g (src e)) (Fin.cons (g (dst e)) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hSC:∀ s i,(SC s).1.val i=rootedCycleOrder (markedRootOrder (l+3) (js s)) (g (row s)) (ps s) i)
    (hVC:∀ z i,(VC z).1.val i=rootedCycleOrder (markedRootOrder (l+3) (jv z)) (f z.1) (pv z) i)
    (hRh:∀ e,(RC e).2.val=hub e) (hSh:∀ s,(SC s).2.val=u s)
    (hVh:∀ z,(VC z).2.val=hub (directedIncidenceEdge (τ z.1 z.2)))
    (hvin:∀ v e,pv ⟨v,Sum.inl e⟩ 0=pr e.val 0∧
      pv ⟨v,Sum.inl e⟩ (Fin.last (l+2))=ps (a v e).val (Fin.last (l+2)))
    (hvout:∀ v e,pv ⟨v,Sum.inr e⟩ 0=ps (d v e).val 0∧
      pv ⟨v,Sum.inr e⟩ (Fin.last (l+2))=pr e.val (Fin.last (l+1)))
    (R R' P:Finset V) (hRR:Disjoint R R') (hPR:Disjoint P (R∪R'))
    (hroots:∀ e,g (src e)∈R∧g (dst e)∈R∧f (src e)∈R'∧f (dst e)∈R')
    (hsroots:∀ s,g (row s)∈R)
    (hprP:∀ e k,pr e k∈P) (hpsP:∀ s k,ps s k∈P)
    (hpv:∀ z k,pv z k∉R∪R'∧
      (pv z k∈P→pv z k∈({pv z 0,pv z (Fin.last (l+2))}:Finset V)))
    (hpr:∀ e e',e≠e'→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr e')))
    (hps:∀ s s',s≠s'→Disjoint (Finset.univ.image (ps s)) (Finset.univ.image (ps s')))
    (hpvdis:∀ z z',z≠z'→Disjoint (Finset.univ.image (pv z)) (Finset.univ.image (pv z')))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s)))
    (hh:Function.Injective hub) (hhu:∀ e s,hub e≠u s)
    (hloop:∀ e,f (dst e)≠f (src e))
    (hr:Function.Injective (fun e=>if jr e then ({g (src e),π (g (dst e))}:Finset V) else {g (src e),g (dst e)}))
    (hs:Function.Injective (fun s=>(g (row s),u s))):
    let C:=Sum.elim RC (Sum.elim SC VC)
    ∀ i j:A⊕(S⊕(Σ v,DirectedIncidence src dst v)),i≠j→
      Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)):=by
  have hRfree:∀ e k,pr e k∉R:=by
    intro e k hx
    exact Finset.disjoint_left.mp hPR (hprP e k) (Finset.mem_union_left _ hx)
  have hSfree:∀ s k,ps s k∉R:=by
    intro s k hx
    exact Finset.disjoint_left.mp hPR (hpsP s k) (Finset.mem_union_left _ hx)
  have hVroot:∀ z:Σ v,DirectedIncidence src dst v,f z.1∈R':=by
    rintro ⟨v,z⟩
    cases z with
    | inl e=>simpa only [e.property] using (hroots e.val).2.2.2
    | inr e=>simpa only [e.property] using (hroots e.val).2.2.1
  have hVR:∀ z:Σ v,DirectedIncidence src dst v,f z.1∉R∪P:=by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · exact Finset.disjoint_left.mp hRR hz (hVroot z)
    · exact Finset.disjoint_left.mp hPR hz (Finset.mem_union_right _ (hVroot z))
  have hpackR:=marked_actual_rim_wheel_packing (l+1) (by omega) hp (fun e=>pr e)
    (fun e=>g (src e)) (fun e=>g (dst e)) jr R RC hRC (fun e=>⟨(hroots e).1,(hroots e).2.1⟩)
    hRfree hpr (by simpa only [hRh] using hh) hr
  have hpackS:=marked_actual_spoke_wheel_packing (l+2) hp (fun s=>ps s)
    (fun s=>g (row s)) js R SC hSC hsroots hSfree hps (by simpa only [hSh] using hs)
  have hpackV:=marked_vertex_wheel_family_packing (l+2) src dst f hub hh hloop τ hp
    (fun z=>pv z) jv R' VC hVC hVh hVroot
    (fun z k hh=>(hpv z k).1 (Finset.mem_union_right _ hh)) hpvdis
  have hown:=marked_attachment_endpoint_ownership (l+1) src dst row a d pr ps (fun z=>pv z)
    hpr hrs hvin hvout
  have hrimavoid:=marked_attachment_rim_hub_avoidance (l+1) src dst
    (fun e he=>hloop e (congrArg f he)) τ hτ hub hh pr (fun z=>pv z) hown
  apply marked_three_family_packing l hp (fun e=>g (src e)) (fun e=>g (dst e))
    (fun s=>g (row s)) (fun z:Σ v,DirectedIncidence src dst v=>f z.1)
    jr js jv (fun e=>pr e) (fun s=>ps s) pv R P RC SC VC hRC hSC hVC
    (fun e=>⟨(hroots e).1,(hroots e).2.1⟩) hsroots hVR hprP
    (fun s k=>⟨hpsP s k,hSfree s k⟩)
    (fun z k=>⟨fun hh=>(hpv z k).1 (Finset.mem_union_left _ hh),(hpv z k).2⟩) hrs
  · intro e s
    simpa only [hRh,hSh] using hhu e s
  · intro e z hz
    simpa only [hRh,hVh] using hrimavoid z e hz
  · intro s z
    simpa only [hSh,hVh] using (hhu (directedIncidenceEdge (τ z.1 z.2)) s).symm
  · exact hpackR
  · exact hpackS
  · exact hpackV

end Oberwolfach
