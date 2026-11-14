module

public import Oberwolfach.MarkedPhysicalLoads
public import Oberwolfach.MarkedCycleUniqueness

@[expose] public section

/-! Marked wheels as sets of actual physical rim and spoke edges.
The permutation is applied only in the supplied physical rim map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

theorem markedCyclePhysicalEdges_injective
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedCyclePhysicalEdges tail head ktail khead m π b) := by
  intro C D he
  apply markedCycleIncidence_injective tail head ktail khead m π b
  funext e
  change markedCycleIncidence tail head ktail khead m C.val e=markedCycleIncidence tail head ktail khead m D.val e
  rw [markedCycleIncidence_physical hp,markedCycleIncidence_physical hp,he]

def markedWheelPhysicalResources
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : Finset (Finset V⊕(V×U)) :=
  (markedCyclePhysicalEdges tail head ktail khead m π b W.1).image Sum.inl ∪
    Finset.univ.image (fun i=>Sum.inr (W.1.val i,W.2.val))

theorem markedWheelPhysicalResources_rim
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : Finset V) :
    Sum.inl e∈markedWheelPhysicalResources W ↔
      e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 := by
  simp [markedWheelPhysicalResources]

theorem markedWheelPhysicalResources_spoke
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (v : V) (u : U) :
    Sum.inr (v,u)∈markedWheelPhysicalResources W ↔
      W.2.val=u ∧ v∈Finset.univ.image W.1.val := by
  simp only [markedWheelPhysicalResources,Finset.mem_union,Finset.mem_image,
    Sum.inl_ne_inr,and_false,exists_false,false_or,Finset.mem_univ,true_and,
    Sum.inr.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨i,hi,hu⟩;exact ⟨hu,i,hi⟩
  · rintro ⟨hu,i,hi⟩;exact ⟨i,hi,hu⟩

theorem markedWheelPhysicalResources_card
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    (markedWheelPhysicalResources W).card=2*(m+1) := by
  have hd : Disjoint
      ((markedCyclePhysicalEdges tail head ktail khead m π b W.1).image (Sum.inl (β:=V×U)))
      (Finset.univ.image (fun i=>Sum.inr (α:=Finset V) (W.1.val i,W.2.val))) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hf
    exact Sum.inr_ne_inl heq
  have hinj : Function.Injective (fun i=>Sum.inr (α:=Finset V) (W.1.val i,W.2.val)) := by
    intro i j he
    exact permutationSeparated_injective π b W.1.val W.1.property.1
      (Prod.mk.inj (Sum.inr.inj he)).1
  rw [markedWheelPhysicalResources,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Sum.inl_injective,
    Finset.card_image_of_injective _ hinj,markedCyclePhysicalEdges_card _ _ _ _ _ _ _ hp,
    Finset.card_univ,Fintype.card_fin]
  omega

theorem markedWheelPhysicalResources_injective
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π) (H₀:=H₀) (Hₖ:=Hₖ) (m:=m) (b:=b)) := by
  intro W Z he
  have hc : W.1=Z.1 := by
    apply markedCyclePhysicalEdges_injective hp
    ext e
    have hh := congrArg (fun S=>Sum.inl e∈S) he
    simpa only [markedWheelPhysicalResources_rim] using (iff_of_eq hh)
  have hs : Sum.inr (W.1.val 0,W.2.val)∈markedWheelPhysicalResources W := by
    rw [markedWheelPhysicalResources_spoke]
    exact ⟨rfl,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  rw [he,markedWheelPhysicalResources_spoke] at hs
  rcases W with ⟨C,u⟩
  rcases Z with ⟨D,v⟩
  change C=D at hc
  subst D
  have hu : u=v := Subtype.ext hs.1.symm
  subst v
  rfl

theorem markedWheelPhysicalResources_spoke_present
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (v : V) (u : U)
    (he : Sum.inr (v,u)∈markedWheelPhysicalResources W) : H₀ v u ∨ Hₖ v u := by
  rw [markedWheelPhysicalResources_spoke] at he
  obtain ⟨i,hi,hiv⟩ := Finset.mem_image.mp he.2
  rw [← hiv,← he.1]
  refine Fin.cases ?_ (fun j=>?_) i
  · exact Or.inr W.2.property.1
  · exact Or.inl (W.2.property.2 j)

theorem markedWheelPhysicalResources_load_rim [Fintype V] [Fintype U]
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) :
    (∑ W,if Sum.inl (markedPhysicalEdge tail head ktail khead π e)∈markedWheelPhysicalResources W then w W else 0)=
      markedWheelRimLoad w e := by
  simp only [markedWheelPhysicalResources_rim]
  exact (markedWheelRimLoad_physical hp w e).symm

theorem markedWheelPhysicalResources_load_spoke [Fintype V] [Fintype U]
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (v : V) (u : U) :
    (∑ W,if Sum.inr (v,u)∈markedWheelPhysicalResources W then w W else 0)=
      markedWheelSpokeLoad w false v u+markedWheelSpokeLoad w true v u := by
  simp only [markedWheelPhysicalResources_spoke]
  exact (markedWheelSpokeLoad_physical w v u).symm


abbrev MarkedActiveEdge (E K : Type*) {V U : Type*} (H₀ Hₖ : V → U → Prop) :=
  (E⊕K)⊕{vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}

def markedActivePhysical (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V)
    (H₀ Hₖ : V → U → Prop) : MarkedActiveEdge E K H₀ Hₖ → Finset V⊕(V×U) :=
  Sum.elim (fun e=>Sum.inl (markedPhysicalEdge tail head ktail khead π e))
    (fun vu=>Sum.inr vu.val)

theorem markedActivePhysical_injective
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedActivePhysical tail head ktail khead π H₀ Hₖ) := by
  intro e f he
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (hp (Sum.inl.inj he))
    | inr f => cases he
  | inr e =>
    cases f with
    | inl f => cases he
    | inr f => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj he))

def markedActiveResources [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : Finset (MarkedActiveEdge E K H₀ Hₖ) :=
  Finset.univ.filter (fun e=>markedActivePhysical tail head ktail khead π H₀ Hₖ e∈markedWheelPhysicalResources W)

theorem markedActiveResources_image [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    (markedActiveResources W).image (markedActivePhysical tail head ktail khead π H₀ Hₖ)=
      markedWheelPhysicalResources W := by
  ext e
  simp only [Finset.mem_image,markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,rfl⟩;exact ha
  · intro he
    cases e with
    | inl e =>
      have hr := (markedWheelPhysicalResources_rim W e).mp he
      obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hr
      let a : MarkedActiveEdge E K H₀ Hₖ := Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 i)
      have heq' : markedActivePhysical tail head ktail khead π H₀ Hₖ a=Sum.inl e :=
        congrArg Sum.inl heq
      exact ⟨a,heq'.symm ▸ he,heq'⟩
    | inr vu =>
      have hp := markedWheelPhysicalResources_spoke_present W vu.1 vu.2 he
      exact ⟨Sum.inr ⟨vu,hp⟩,he,rfl⟩

theorem markedActiveResources_card [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    (markedActiveResources W).card=2*(m+1) := by
  have hh := congrArg Finset.card (markedActiveResources_image W)
  rw [Finset.card_image_of_injective _ (markedActivePhysical_injective hp),
    markedWheelPhysicalResources_card hp] at hh
  exact hh

theorem markedActiveResources_injective [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedActiveResources (tail:=tail) (head:=head) (ktail:=ktail)
      (khead:=khead) (π:=π) (m:=m) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)) := by
  intro W Z he
  apply markedWheelPhysicalResources_injective hp
  rw [← markedActiveResources_image W,← markedActiveResources_image Z,he]

theorem marked_active_exact_loads [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hR : ∀ e,markedWheelRimLoad w e=1)
    (hS : ∀ j v u,markedWheelSpokeLoad w j v u=
      if j then (if Hₖ v u then 1 else 0) else (if H₀ v u then 1 else 0))
    (e : MarkedActiveEdge E K H₀ Hₖ) :
    (∑ W,if e∈markedActiveResources W then w W else 0)=1 := by
  simp only [markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and]
  cases e with
  | inl e =>
    change (∑ W,if Sum.inl (markedPhysicalEdge tail head ktail khead π e)∈markedWheelPhysicalResources W then w W else 0)=1
    rw [markedWheelPhysicalResources_load_rim hp,hR]
  | inr vu =>
    change (∑ W,if Sum.inr (vu.val.1,vu.val.2)∈markedWheelPhysicalResources W then w W else 0)=1
    simp only [markedWheelPhysicalResources_spoke]
    exact markedWheelSpokeLoad_physical_exact hdisj w hS vu.val.1 vu.val.2 vu.property

theorem markedActiveResources_rim [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : E⊕K) :
    Sum.inl e∈markedActiveResources W ↔
      markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 := by
  simp only [markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and,
    markedActivePhysical,Sum.elim_inl,markedWheelPhysicalResources_rim]

theorem markedActiveResources_spoke [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}) :
    Sum.inr vu∈markedActiveResources W ↔ W.2.val=vu.val.2 ∧ vu.val.1∈Set.range W.1.val := by
  simp only [markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and,
    markedActivePhysical,Sum.elim_inr]
  simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using
    markedWheelPhysicalResources_spoke W vu.val.1 vu.val.2

end Oberwolfach
