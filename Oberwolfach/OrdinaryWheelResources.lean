module

public import Oberwolfach.OrdinaryPotentialLoads
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! Actual ordinary wheels are distinct 2r-element subsets of the physical
rim/spoke edge set. Their physical edge loads agree with the two load maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem IsEmbeddedCycle.edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    {C : SimpleGraph V} {r : ℕ} (hC : IsEmbeddedCycle C r) : C.edgeFinset.card=r := by
  have hd (v : V) : C.degree v=if v∈C.support then 2 else 0 := by
    rcases hC.degree_zero_or_two v with hz|ht
    · rw [hz,if_neg ((C.degree_eq_zero_iff_notMem_support v).mp hz)]
    · have hv : v∈C.support := by
        by_contra hv
        have hh := (C.degree_eq_zero_iff_notMem_support v).mpr hv
        omega
      rw [ht,if_pos hv]
  have hh := C.sum_degrees_eq_twice_card_edges
  have he : (∑ v,C.degree v)=r*2 := by
    simp only [hd]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun v=>v∈C.support)=C.support.toFinset := by ext;simp
    rw [hf,Finset.sum_const,hC.support_card,smul_eq_mul]
  omega

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {P F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}

theorem ordinaryWheelResources_card (W : OrdinaryWheel P F H r) :
    (ordinaryWheelResources W).card=2*r := by
  have hC : IsEmbeddedCycle (ordinaryWheelRim W) r := W.val.1.val.property
  have hd : Disjoint ((ordinaryWheelRim W).edgeFinset.image (Sum.inl (β:=V×U)))
      ((ordinaryWheelRim W).support.toFinset.image (fun v=>Sum.inr (v,ordinaryWheelHub W))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b,_,hh⟩ := Finset.mem_image.mp hf
    cases hh
  unfold ordinaryWheelResources
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ (by intro a b h;exact (Prod.mk.inj (Sum.inr.inj h)).1),
    hC.edgeFinset_card,hC.support_card]
  omega

theorem ordinaryWheelResources_injective :
    Function.Injective (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=H) (r:=r)) := by
  intro W Z he
  have hc : ordinaryWheelRim W=ordinaryWheelRim Z := by
    apply SimpleGraph.ext
    funext x y
    have h := congrArg (fun S=>Sum.inl s(x,y)∈S) he
    simpa only [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet] using h
  have hC : IsEmbeddedCycle (ordinaryWheelRim W) r := W.val.1.val.property
  obtain ⟨x,y,hxy⟩ := hC.exists_adj
  have hs : Sum.inr (x,ordinaryWheelHub W)∈ordinaryWheelResources W :=
    (ordinaryWheelResources_spoke W x _).mpr ⟨rfl,hxy.mem_support_left⟩
  rw [he,ordinaryWheelResources_spoke] at hs
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Subtype.ext hc
  · exact hs.1.symm

theorem ordinaryWheelResources_load_rim (w : OrdinaryWheel P F H r → ℝ) (x y : V) :
    (∑ W,if Sum.inl s(x,y)∈ordinaryWheelResources W then w W else 0)=ordinaryRimLoad w x y := by
  unfold ordinaryRimLoad
  apply Finset.sum_congr rfl
  intro W _
  simp only [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet]

theorem ordinaryWheelResources_load_spoke (w : OrdinaryWheel P F H r → ℝ) (v : V) (u : U) :
    (∑ W,if Sum.inr (v,u)∈ordinaryWheelResources W then w W else 0)=ordinarySpokeLoad w v u := by
  unfold ordinarySpokeLoad
  apply Finset.sum_congr rfl
  intro W _
  simp only [ordinaryWheelResources_spoke]

end Oberwolfach
