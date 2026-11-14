module

public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.TransformerOriginalEdgeIdentity

@[expose] public section

/-! Integer resource identities for actual marked wheels. Every coordinate
is a physical rim edge or an actual row--hub spoke. Position sums are valid
because the supplied host map is injective, not because labels are silently
identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ Hₖ:V→U→Prop}

 def markedWheelPositionResource
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ):
    Fin (m+1)⊕Fin (m+1)→Finset V⊕(V×U)
  | Sum.inl i=>Sum.inl (markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b W.1 i))
  | Sum.inr i=>Sum.inr (W.1.val i,W.2.val)

 theorem markedWheelPositionResource_injective
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ):
    Function.Injective (markedWheelPositionResource W):=by
  intro i j h
  cases i with
  | inl i=>
    cases j with
    | inl j=>
      exact congrArg Sum.inl (markedCycle_distinct_physical_edges tail head ktail khead m π b hp W.1 (Sum.inl.inj h))
    | inr j=>cases h
  | inr i=>
    cases j with
    | inl j=>cases h
    | inr j=>
      exact congrArg Sum.inr (permutationSeparated_injective π b W.1.val W.1.property.1
        (congrArg Prod.fst (Sum.inr.inj h)))

 theorem markedWheelPositionResource_image
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ):
    Finset.univ.image (markedWheelPositionResource W)=markedWheelPhysicalResources W:=by
  ext e
  cases e with
  | inl e=>
    rw [markedWheelPhysicalResources_rim]
    simp only [markedCyclePhysicalEdges,Finset.mem_image,Finset.mem_univ,true_and,Function.comp_apply]
    constructor
    · rintro ⟨i,hi⟩
      cases i with
      | inl i=>exact ⟨i,Sum.inl.inj hi⟩
      | inr i=>cases hi
    · rintro ⟨i,hi⟩
      exact ⟨Sum.inl i,congrArg Sum.inl hi⟩
  | inr vu=>
    rw [markedWheelPhysicalResources_spoke]
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩
      cases i with
      | inl i=>cases hi
      | inr i=>
        have hh:=Prod.mk.inj (Sum.inr.inj hi)
        exact ⟨hh.2,i,hh.1⟩
    · rintro ⟨hu,i,hi⟩
      exact ⟨Sum.inr i,congrArg Sum.inr (Prod.ext hi hu)⟩

 theorem markedWheelPhysicalResources_integer_positions
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)=
      (∑ i,if e=markedWheelPositionResource W (Sum.inl i) then 1 else 0)+
      ∑ i,if e=markedWheelPositionResource W (Sum.inr i) then 1 else 0:=by
  have hh:=injective_image_integer_indicator (markedWheelPositionResource W) (markedWheelPositionResource_injective hp W) e
  rw [Fintype.sum_sum_type,markedWheelPositionResource_image] at hh
  exact hh.symm

 theorem markedWheelPhysicalResources_integer_difference
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W W':MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources W' then 1 else 0)=
      (∑ i,physicalIntDelta (markedWheelPositionResource W (Sum.inl i))
        (markedWheelPositionResource W' (Sum.inl i)) e)+
      ∑ i,physicalIntDelta (markedWheelPositionResource W (Sum.inr i))
        (markedWheelPositionResource W' (Sum.inr i)) e:=by
  rw [markedWheelPhysicalResources_integer_positions hp,markedWheelPhysicalResources_integer_positions hp]
  simp only [physicalIntDelta,Finset.sum_sub_distrib]
  ring

 theorem markedWheelPositionResource_rim_formula
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ) (i:Fin (m+1)):
    markedWheelPositionResource W (Sum.inl i)=
      Sum.inl (if i=Fin.last m then {W.1.val i,π (W.1.val 0)}
        else {W.1.val i,W.1.val (finRotate (m+1) i)}):=by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [markedWheelPositionResource,markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr,ite_true]
    obtain ⟨ht,hh⟩:=Classical.choose_spec W.1.property.2.2
    rw [ht,hh]
  · simp only [markedWheelPositionResource,markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,
      Sum.elim_inl,Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ]
    obtain ⟨ht,hh⟩:=Classical.choose_spec (W.1.property.2.1 j)
    rw [ht,hh]

end Oberwolfach
