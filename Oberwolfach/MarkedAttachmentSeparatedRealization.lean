module

public import Oberwolfach.MarkedAttachmentRealization
public import Oberwolfach.IndexedMarkedRealizationGeometry
public import Oberwolfach.MarkedWheelExtensionRealization
public import Oberwolfach.MarkedAttachedWheelPacking

@[expose] public section

/-! The attachment end of the marked absorber. The actual expanded graph
has precisely the old resources and a disjoint, decomposable wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_attachment_realization_separated
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S)
    (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (W Z:Finset V) (B:Finset U) (hr:∀ v,R.rows v∈Z) (hh:∀ u,R.hubs u∈B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card (A⊕S)*(l+5)+l+12)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card (A⊕S)<ch):
    ∃ T:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega)) tail head ktail khead H₀ HK π b,
    ∃ extra:Finset (Finset V⊕(V×U)),
      T.resources=R.resources∪extra∧Disjoint R.resources extra∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) extra∧
      (∀ e∈extra,¬MarkedOldResource tail head ktail khead π Z B e)∧
      (∀ v,T.rows (.inl v)=R.rows v)∧(∀ u,T.hubs (.inl u)=R.hubs u)∧
      (∀ i,T.hubs (.inr i)∉B)∧
      (∀ i k,k≠markedAttachmentPosition l G.jr G.js i→
        T.rows (.inr (i,k))∉W∧T.rows (.inr (i,k))∉Z∧∀ z∈Z,¬PermutationClose π b (T.rows (.inr (i,k))) z)∧
      (∀ i,T.rows (.inr (i,markedAttachmentPosition l G.jr G.js i))=Sum.elim (R.rows∘G.src) (R.rows∘G.row) i)∧
      (∀ v,T.rows v∉R.rowSet→∀ z∈Z,¬PermutationClose π b (T.rows v) z)∧
      (∀ v w,T.rows v∉R.rowSet→T.rows w∉R.rowSet→T.rows v≠T.rows w→
        ¬PermutationClose π b (T.rows v) (T.rows w)):=by
  obtain ⟨C,hC,hCB,hCi,hav,hdis,hsep⟩:=marked_attachment_wheel_families Q hl
    (R.rows∘G.src) (R.rows∘G.row) G.jr G.js W Z B (fun a=>hr _) (fun s=>hr _) hbudget hB
  have hroot:∀ i,(C i).1.val (markedAttachmentPosition l G.jr G.js i)∈Z:=by
    intro i;rw [hC];cases i <;> exact hr _
  have hpack:=marked_attached_wheels_pack hp (by omega) C (markedAttachmentPosition l G.jr G.js)
    Z hroot (fun i k hk=>(hav i k hk).2.1) hCi hdis
  have hold:∀ i,Disjoint (markedWheelPhysicalResources (C i)) R.resources:=by
    intro i
    exact marked_attached_wheel_disjoint_old_graph hp (by omega) (C i) _ Z B
      (fun k hk=>(hav i k hk).2.1) (hCB i) (R.rows∘G.src) (R.rows∘G.dst) (R.rows∘G.row) G.jr (R.hubs∘G.hub)
      (fun a=>⟨hr _,hr _⟩) (fun s=>⟨hr _,hh _⟩) R.rimPresent
  let T:=indexedMarkedAttachmentRealization G R hp C hC hpack hold
  let extra:=Finset.univ.biUnion (fun i=>markedWheelPhysicalResources (C i))
  have hfree (v) (hv:T.rows v∉R.rowSet):∃ i k,k≠markedAttachmentPosition l G.jr G.js i∧T.rows v=(C i).1.val k:=by
    cases v with
    | inl v=>exact (hv (R.row_mem v)).elim
    | inr p=>
      by_cases hk:p.2=markedAttachmentPosition l G.jr G.js p.1
      · apply (hv ?_).elim
        change (C p.1).1.val p.2∈R.rowSet
        rw [hk,hC]
        cases p.1 <;> exact R.row_mem _
      · exact ⟨p.1,p.2,hk,rfl⟩
  refine ⟨T,extra,indexedMarkedAttachmentRealization_resources G R hp C hC hpack hold,?_,
    resource_indexed_family_decomposition markedWheelPhysicalResources C hpack,?_,fun _=>rfl,fun _=>rfl,hCB,hav,hC,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hold i) hi he
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact marked_wheel_without_old_resources hp (C i) Z B
      (marked_one_old_position_no_old_arc (by omega) (C i).1 _ Z (fun k hk=>(hav i k hk).2.1)) (hCB i) e hi
  · intro v hv z hz
    obtain ⟨i,k,hk,heq⟩:=hfree v hv
    rw [heq]
    exact (hav i k hk).2.2 z hz
  · intro v w hv hw hne
    obtain ⟨i,k,hk,heq⟩:=hfree v hv
    obtain ⟨j,k',hk',heq'⟩:=hfree w hw
    rw [heq,heq']
    apply hsep i j k k' hk hk'
    intro h
    cases h
    exact hne (heq.trans heq'.symm)

end Oberwolfach
