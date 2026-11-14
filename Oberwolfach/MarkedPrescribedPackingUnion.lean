module

public import Oberwolfach.MarkedSparseInnerEdgePacking
public import Oberwolfach.MarkedPackingUnions

@[expose] public section

/-! The two constructed prescribed-edge families form one actual physical
packing. Its inner intersection and all three degree bounds refer to that
same union, so no disjointness or cumulative-loss input is added later. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U] {tail head:E→V} {ktail khead:K→V}
  {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_two_families_packing
    (R:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (S:J→MarkedWheel tail head ktail khead m π b H₀ HK)
    (hRR:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (R j)))
    (hSS:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (S i)) (markedWheelPhysicalResources (S j)))
    (hRS:∀ i j,Disjoint (markedWheelPhysicalResources (R i)) (markedWheelPhysicalResources (S j))):
    ∀ W∈Finset.univ.image R∪Finset.univ.image S,
      ∀ Z∈Finset.univ.image R∪Finset.univ.image S,W≠Z→
        Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=by
  intro W hW Z hZ hne
  rcases Finset.mem_union.mp hW with hW|hW <;>
    rcases Finset.mem_union.mp hZ with hZ|hZ
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hRR i j (fun h=>hne (congrArg R h))
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hRS i j
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact (hRS j i).symm
  · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hZ
    exact hSS i j (fun h=>hne (congrArg S h))

theorem marked_two_families_inner_intersection
    (R:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (S:J→MarkedWheel tail head ktail khead m π b H₀ HK)
    (X:Finset V) (Z:Finset U) (er:I→Finset V) (es:J→V×U)
    (hR:∀ i,(markedWheelPhysicalResources (R i)).filter (markedInnerResource X Z)={Sum.inl (er i)})
    (hS:∀ i,(markedWheelPhysicalResources (S i)).filter (markedInnerResource X Z)={Sum.inr (es i)}):
    ((Finset.univ.image R∪Finset.univ.image S).biUnion markedWheelPhysicalResources).filter (markedInnerResource X Z)=
      Finset.univ.image (fun i=>Sum.inl (er i))∪Finset.univ.image (fun i=>Sum.inr (es i)):=by
  ext e
  have hr (i:I):e∈markedWheelPhysicalResources (R i)∧markedInnerResource X Z e↔e=Sum.inl (er i):=by
    simpa only [Finset.mem_filter,Finset.mem_singleton] using Iff.of_eq (congrArg (fun A=>e∈A) (hR i))
  have hs (i:J):e∈markedWheelPhysicalResources (S i)∧markedInnerResource X Z e↔e=Sum.inr (es i):=by
    simpa only [Finset.mem_filter,Finset.mem_singleton] using Iff.of_eq (congrArg (fun A=>e∈A) (hS i))
  simp only [Finset.mem_filter,Finset.mem_biUnion,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨W,(⟨i,rfl⟩|⟨j,rfl⟩),he⟩,hi⟩
    · exact Or.inl ⟨i,((hr i).mp ⟨he,hi⟩).symm⟩
    · exact Or.inr ⟨j,((hs j).mp ⟨he,hi⟩).symm⟩
  · rintro (⟨i,rfl⟩|⟨j,rfl⟩)
    · have h:=(hr i).mpr rfl
      exact ⟨⟨R i,Or.inl ⟨i,rfl⟩,h.1⟩,h.2⟩
    · have h:=(hs j).mpr rfl
      exact ⟨⟨S j,Or.inr ⟨j,rfl⟩,h.1⟩,h.2⟩

theorem marked_two_families_degree_bounds
    (R:I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (S:J→MarkedWheel tail head ktail khead m π b H₀ HK)
    (aR aS bR bS cR cS:ℝ)
    (hRr:∀ v,((markedFamilyRim R).degree v:ℝ)≤aR)
    (hSr:∀ v,((markedFamilyRim S).degree v:ℝ)≤aS)
    (hRs:∀ v,((Finset.univ.filter (markedFamilySpokes R v)).card:ℝ)≤bR)
    (hSs:∀ v,((Finset.univ.filter (markedFamilySpokes S v)).card:ℝ)≤bS)
    (hRc:∀ u,((Finset.univ.filter (fun v=>markedFamilySpokes R v u)).card:ℝ)≤cR)
    (hSc:∀ u,((Finset.univ.filter (fun v=>markedFamilySpokes S v u)).card:ℝ)≤cS):
    let M:=Finset.univ.image R∪Finset.univ.image S
    (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤aR+aS)∧
    (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤bR+bS)∧
    (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤cR+cS):=by
  let M:=Finset.univ.image R∪Finset.univ.image S
  have hsp (v:V) (u:U):markedPackingSpokes M v u↔markedFamilySpokes R v u∨markedFamilySpokes S v u:=by
    simp only [M,markedPackingSpokes_union,marked_family_image_spokes]
  refine ⟨?_,?_,?_⟩
  · intro v
    have hgraph:markedPackingRimGraph M=markedFamilyRim R⊔markedFamilyRim S:=by
      simp only [M,markedPackingRimGraph_union,marked_family_image_rim]
    have hle:((markedPackingRimGraph M).degree v:ℝ)≤
        (markedFamilyRim R).degree v+(markedFamilyRim S).degree v:=by
      have hh:(markedPackingRimGraph M).degree v≤
          (markedFamilyRim R).degree v+(markedFamilyRim S).degree v:=by
        rw [hgraph]
        convert graph_degree_sup_le (markedFamilyRim R) (markedFamilyRim S) v using 1 <;> congr!
      exact_mod_cast hh
    exact hle.trans (add_le_add (hRr v) (hSr v))
  · intro v
    have he:Finset.univ.filter (markedPackingSpokes M v)=
        Finset.univ.filter (markedFamilySpokes R v)∪Finset.univ.filter (markedFamilySpokes S v):=by
      ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,hsp]
    rw [he]
    have hh:((Finset.univ.filter (markedFamilySpokes R v)∪Finset.univ.filter (markedFamilySpokes S v)).card:ℝ)≤
        (Finset.univ.filter (markedFamilySpokes R v)).card+(Finset.univ.filter (markedFamilySpokes S v)).card:=by
      exact_mod_cast Finset.card_union_le (Finset.univ.filter (markedFamilySpokes R v)) (Finset.univ.filter (markedFamilySpokes S v))
    exact hh.trans (add_le_add (hRs v) (hSs v))
  · intro u
    have he:Finset.univ.filter (fun v=>markedPackingSpokes M v u)=
        Finset.univ.filter (fun v=>markedFamilySpokes R v u)∪Finset.univ.filter (fun v=>markedFamilySpokes S v u):=by
      ext v;simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,hsp]
    rw [he]
    have hh:((Finset.univ.filter (fun v=>markedFamilySpokes R v u)∪Finset.univ.filter (fun v=>markedFamilySpokes S v u)).card:ℝ)≤
        (Finset.univ.filter (fun v=>markedFamilySpokes R v u)).card+(Finset.univ.filter (fun v=>markedFamilySpokes S v u)).card:=by
      exact_mod_cast Finset.card_union_le (Finset.univ.filter (fun v=>markedFamilySpokes R v u)) (Finset.univ.filter (fun v=>markedFamilySpokes S v u))
    exact hh.trans (add_le_add (hRc u) (hSc u))

end Oberwolfach
