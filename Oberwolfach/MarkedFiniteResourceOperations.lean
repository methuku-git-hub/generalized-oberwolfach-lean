module

public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.MarkedPackingFiniteBalance
public import Oberwolfach.MarkedActualRowResources
public import Oberwolfach.MarkedOldInnerAgreement

@[expose] public section

/-! Exact physical resources of finite original occurrence sets. These
identities connect divisibility calculations with induced-pair and star
conditions, retaining the injectivity requirement on physical rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)

def markedFiniteResources (A:Finset (E⊕K)) (S:Finset (V×U)):Finset (Finset V⊕(V×U)):=
  A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr

theorem markedFiniteResources_rim
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (a:E⊕K):
    Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈markedFiniteResources tail head ktail khead π A S↔a∈A:=by
  simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,
    and_false,exists_false,or_false]
  constructor
  · rintro ⟨b,hb,he⟩;exact hp he ▸ hb
  · intro ha;exact ⟨a,ha,rfl⟩

theorem markedFiniteResources_spoke (A:Finset (E⊕K)) (S:Finset (V×U)) (z:V×U):
    Sum.inr z∈markedFiniteResources tail head ktail khead π A S↔z∈S:=by
  simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inr.injEq,Sum.inl_ne_inr,
    and_false,exists_false,false_or]
  constructor
  · rintro ⟨a,ha,rfl⟩;exact ha
  · intro hz;exact ⟨z,hz,rfl⟩

theorem markedFiniteResources_sdiff
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A B:Finset (E⊕K)) (S T:Finset (V×U)):
    markedFiniteResources tail head ktail khead π (A\B) (S\T)=
      markedFiniteResources tail head ktail khead π A S\markedFiniteResources tail head ktail khead π B T:=by
  unfold markedFiniteResources
  have hf:Function.Injective (fun a:E⊕K=>(Sum.inl (markedPhysicalEdge tail head ktail khead π a):Finset V⊕(V×U))):=fun _ _ he=>hp (Sum.inl.inj he)
  rw [Finset.image_sdiff _ _ hf,Finset.image_sdiff _ _ Sum.inr_injective]
  ext z
  cases z <;> simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_image,
    Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,and_false,exists_false,
    or_false,false_or,not_false_eq_true,and_true,false_and]

theorem markedFiniteResources_star
    (A:Finset (E⊕K)) (S:Finset (V×U)) (T:Finset V) (W:Finset U)
    (hT:∀ x,π x∈T↔x∈T):
    markedFiniteResources tail head ktail khead π
      (A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T))
      (S.filter (fun z=>z.1∈T∨z.2∈W))=
      (markedFiniteResources tail head ktail khead π A S).filter (markedStarResource T W):=by
  unfold markedFiniteResources
  rw [Finset.filter_union,Finset.filter_image,Finset.filter_image]
  congr 1
  · congr 1
    ext a
    simp only [Finset.mem_filter,marked_physical_rim_star_iff tail head ktail khead π T W hT]
  · congr 1
    ext z
    simp only [Finset.mem_filter,markedStarResource,Sum.elim_inr]

theorem markedFiniteResources_inner
    (A:Finset (E⊕K)) (S:Finset (V×U)) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I):
    markedFiniteResources tail head ktail khead π
      (A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))
      (S.filter (fun z=>z.1∈I∧z.2∈J))=
      (markedFiniteResources tail head ktail khead π A S).filter (markedInnerResource I J):=by
  unfold markedFiniteResources
  rw [Finset.filter_union,Finset.filter_image,Finset.filter_image]
  congr 1
  · congr 1
    ext a
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inl,marked_physical_edge_inner_iff I hI]
  · congr 1
    ext z
    simp only [Finset.mem_filter,markedInnerResource,Sum.elim_inr]

variable {m b:ℕ} {H₀ HK:V→U→Prop}

theorem markedPackingResources_eq_finite
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    markedFiniteResources tail head ktail khead π (M.biUnion markedWheelArcs) (M.biUnion markedWheelSpokePairs)=
      M.biUnion markedWheelPhysicalResources:=by
  ext z
  cases z with
  | inl e=>
    simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inl.injEq,Sum.inr_ne_inl,
      and_false,exists_false,or_false,Finset.mem_biUnion,markedWheelPhysicalResources_rim]
    constructor
    · rintro ⟨a,⟨W,hW,ha⟩,he⟩
      have hr:=(markedWheelPhysicalResources_rim W _).mp (markedWheel_arc_resource W a ha)
      exact ⟨W,hW,he ▸ hr⟩
    · rintro ⟨W,hW,he⟩
      obtain ⟨i,hi,he⟩:=Finset.mem_image.mp he
      exact ⟨markedCycleTypedEdge tail head ktail khead m π b W.1 i,
        ⟨W,hW,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩,he⟩
  | inr z=>
    rw [markedFiniteResources_spoke]
    simp only [Finset.mem_biUnion,markedWheel_spoke_resource]

end Oberwolfach
