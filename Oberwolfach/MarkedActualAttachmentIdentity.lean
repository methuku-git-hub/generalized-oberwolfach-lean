module

public import Oberwolfach.MarkedVertexPairIdentity
public import Oberwolfach.MarkedRimPairIdentity
public import Oberwolfach.MarkedAttachmentIdentity

@[expose] public section

/-! Global attachment cancellation for the actual marked wheel families.
The incoming and outgoing attachment rules retain their different types,
and every physical marked edge retains the successor on its head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype A] [Fintype S] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_actual_attachment_integer_identity (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (src dst:A→V) (row:S→V) (φ:V→V) (hub:A→U) (u u':S→U) (jr:A→Bool) (js:S→Bool)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (σ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (pr:A→Fin (n+1)→V) (ps:S→Fin (n+2)→V)
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
    (e:Finset V⊕(V×U)):
    (∑ i:A,((if e∈markedWheelPhysicalResources (RC i) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (RD i) then 1 else 0)))+
    (∑ s:S,((if e∈markedWheelPhysicalResources (SC s) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (SD s) then 1 else 0)))-
    (∑ z:Σ v,DirectedIncidence src dst v,((if e∈markedWheelPhysicalResources (VC z) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (VD z) then 1 else 0)))=
    (∑ i:A,physicalIntDelta (Sum.inl (if jr i then {src i,π (dst i)} else {src i,dst i}))
      (Sum.inl (if jr i then {φ (src i),π (φ (dst i))} else {φ (src i),φ (dst i)})) e)+
    (∑ s:S,physicalIntDelta (Sum.inr (row s,u s)) (Sum.inr (φ (row s),u' s)) e)+
    ∑ s:S,∑ k:Fin (n+2),physicalIntDelta (Sum.inr (ps s k,u s)) (Sum.inr (ps s k,u' s)) e:=by
  let core:A→ℤ:=fun i=>physicalIntDelta
    (Sum.inl (if jr i then {src i,π (dst i)} else {src i,dst i}))
    (Sum.inl (if jr i then {φ (src i),π (φ (dst i))} else {φ (src i),φ (dst i)})) e
  let ri:A→ℤ:=fun i=>physicalIntDelta (Sum.inl {dst i,pr i 0}) (Sum.inl {φ (dst i),pr i 0}) e
  let ro:A→ℤ:=fun i=>physicalIntDelta (Sum.inl {pr i (Fin.last n),src i})
    (Sum.inl {pr i (Fin.last n),φ (src i)}) e
  let cross:S→ℤ:=fun s=>physicalIntDelta (Sum.inr (row s,u s)) (Sum.inr (φ (row s),u' s)) e
  let si:S→ℤ:=fun s=>physicalIntDelta
    (Sum.inl (if js s then {ps s (Fin.last (n+1)),π (row s)} else {ps s (Fin.last (n+1)),row s}))
    (Sum.inl (if js s then {ps s (Fin.last (n+1)),π (φ (row s))} else {ps s (Fin.last (n+1)),φ (row s)})) e
  let so:S→ℤ:=fun s=>physicalIntDelta (Sum.inl {row s,ps s 0}) (Sum.inl {φ (row s),ps s 0}) e
  let load:S→ℤ:=fun s=>∑ k:Fin (n+2),physicalIntDelta (Sum.inr (ps s k,u s)) (Sum.inr (ps s k,u' s)) e
  let hubdelta:A→V→ℤ:=fun i v=>physicalIntDelta (Sum.inr (v,hub i)) (Sum.inr (φ v,hub i)) e
  have hR:∀ i:A,(if e∈markedWheelPhysicalResources (RC i) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (RD i) then 1 else 0)=
      core i+ri i+ro i+hubdelta i (dst i)+hubdelta i (src i):=by
    intro i
    have hh:=marked_rim_pair_integer_identity n hn hp (pr i) (src i) (dst i) (φ (src i)) (φ (dst i))
      (hub i) (jr i) (RC i) (RD i) (hRC i) (hRD i) (hRh i).1 (hRh i).2 e
    exact hh.trans (by dsimp [core,ri,ro,hubdelta];abel)
  have hS:∀ s:S,(if e∈markedWheelPhysicalResources (SC s) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (SD s) then 1 else 0)=cross s+si s+so s+load s:=by
    intro s
    have hh:=marked_spoke_pair_integer_identity (n+1) (by omega) hp (ps s) (row s) (φ (row s))
      (u s) (u' s) (js s) (SC s) (SD s) (hSC s) (hSD s) (hSh s).1 (hSh s).2 e
    exact hh.trans (by dsimp [cross,si,so,load];abel)
  have hV:∀ v,∀ z:DirectedIncidence src dst v,
      (if e∈markedWheelPhysicalResources (VC ⟨v,z⟩) then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources (VD ⟨v,z⟩) then 1 else 0)=
      (Sum.elim (fun i:{i:A // dst i=v}=>ri i.val) (fun i:{i:A // src i=v}=>ro i.val)) z+
      (Sum.elim (fun i:{i:A // dst i=v}=>si (a v i).val)
        (fun i:{i:A // src i=v}=>so (d v i).val)) z+
      hubdelta (directedIncidenceEdge (σ v z)) v:=by
    intro v z
    have hh:=marked_vertex_pair_integer_identity (n+1) (by omega) hp (pv ⟨v,z⟩) v (φ v)
      (hub (directedIncidenceEdge (σ v z))) (jv ⟨v,z⟩) (VC ⟨v,z⟩) (VD ⟨v,z⟩)
      (hVC ⟨v,z⟩) (hVD ⟨v,z⟩) (hVh ⟨v,z⟩).1 (hVh ⟨v,z⟩).2 e
    cases z with
    | inl i=>
      rw [(hvin v i).1,(hvin v i).2.1,(hvin v i).2.2] at hh
      simpa only [Sum.elim_inl,ri,si,hubdelta,i.property,(a v i).property] using hh
    | inr i=>
      rw [(hvout v i).1,(hvout v i).2.1,(hvout v i).2.2] at hh
      simp only [Bool.false_eq_true,ite_false] at hh
      exact hh.trans (by dsimp [ro,so,hubdelta];rw [i.property,(d v i).property];abel)
  rw [Fintype.sum_sigma]
  simp_rw [hR,hS,hV]
  convert marked_attachment_integer_identity src dst row a d σ core ri ro cross si so load hubdelta using 1 <;> congr!

end Oberwolfach
