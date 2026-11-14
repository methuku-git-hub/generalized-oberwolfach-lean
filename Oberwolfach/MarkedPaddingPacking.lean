module

public import Oberwolfach.MarkedPaddingWheelFamilies
public import Oberwolfach.MarkedSpokeWheelPacking
public import Oberwolfach.MarkedResourceSupport

@[expose] public section

/-! Added wheels remain physically edge-disjoint even when several old
marked heads coincide. No edge of such a wheel has both auxiliary ends
among the old rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ HK:V→U→Prop}

theorem marked_padding_no_old_arc (hm:0<m)
    (W:MarkedWheel tail head ktail khead m π b H₀ HK) (v:V) (p:Fin m↪V) (Z:Finset V)
    (hW:∀ a,W.1.val a=Fin.cons (α:=fun _=>V) v p a) (hav:∀ a,p a∉Z):
    ∀ a,¬(W.1.val a∈Z∧W.1.val (finRotate (m+1) a)∈Z):=by
  intro a
  refine Fin.cases ?_ (fun k=>?_) a
  · intro h
    let z:Fin m:=⟨0,hm⟩
    have he:(0:Fin (m+1))=z.castSucc:=rfl
    have hh:=h.2
    rw [he,finRotate_castSucc_eq_succ,hW,Fin.cons_succ] at hh
    exact hav z hh
  · intro h
    have hh:=h.1
    rw [hW,Fin.cons_succ] at hh
    exact hav k hh

theorem marked_padding_family_packing (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v:I→V) (p:I→(Fin m↪V)) (Z:Finset V) (hv:∀ i,v i∈Z)
    (hW:∀ i a,(W i).1.val a=Fin.cons (α:=fun _=>V) (v i) (p i) a)
    (hav:∀ i a,p i a∉Z)
    (hdis:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j)))
    (hh:Function.Injective (fun i=>(W i).2.val)):
    ∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W j)):=by
  apply marked_wheel_packing_of_distinct_hubs W hh
  apply marked_cycle_family_packing_no_old_arc hp (fun i=>(W i).1) Z (fun i=>Finset.univ.image (p i))
  · intro i a
    rw [hW]
    refine Fin.cases ?_ (fun k=>?_) a
    · exact Finset.mem_union_left _ (hv i)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  · exact hdis
  · intro i
    exact marked_padding_no_old_arc hm (W i) (v i) (p i) Z (hW i) (hav i)

theorem marked_padding_avoids_old_resources (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (v:V) (p:Fin m↪V) (Z:Finset V) (B:Finset U)
    (hW:∀ a,W.1.val a=Fin.cons (α:=fun _=>V) v p a) (hav:∀ a,p a∉Z)
    (hh:W.2.val∉B) (L:Finset (Finset V⊕(V×U)))
    (hL:∀ e∈L,match e with
      | Sum.inl e=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=e∧
          Sum.elim tail ktail a∈Z∧Sum.elim head khead a∈Z
      | Sum.inr z=>z.2∈B):
    Disjoint (markedWheelPhysicalResources W) L:=by
  apply Finset.disjoint_left.mpr
  intro e he hle
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩:=hL _ hle
    have hw: e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1:=
      (markedWheelPhysicalResources_rim W e).mp he
    obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hw
    have hka:=hp (hk.trans ha.symm)
    have ht:=markedCycleTypedEdge_endpoints tail head ktail khead m π b W.1 k
    rw [hka] at ht
    exact marked_padding_no_old_arc hm W v p Z hW hav k ⟨ht.1 ▸ hat,ht.2 ▸ hah⟩
  | inr z=>
    have hz:W.2.val=z.2:=((markedWheelPhysicalResources_spoke W z.1 z.2).mp he).1
    exact hh (hz ▸ hL _ hle)

end Oberwolfach
