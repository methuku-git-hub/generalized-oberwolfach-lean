module

public import Oberwolfach.MarkedWheelResources

@[expose] public section

/-! Auxiliary and physical incident-edge tests on the same marked resource
space. The marked head is twisted only in the physical test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem paired_fiber_card {A X Y : Type*} [Fintype A] [Fintype Y]
    (f : A → X) (g : A → Y) (hinj : Function.Injective (fun a=>(f a,g a))) (x : X) :
    (Finset.univ.filter (fun a=>f a=x)).card≤Fintype.card Y := by
  classical
  have hi : Set.InjOn g (↑(Finset.univ.filter (fun a=>f a=x)):Set A) := by
    intro a ha b hb he
    have ha' : f a=x := (Finset.mem_filter.mp ha).2
    have hb' : f b=x := (Finset.mem_filter.mp hb).2
    exact hinj (Prod.ext (ha'.trans hb'.symm) he)
  rw [← Finset.card_image_of_injOn hi]
  exact Finset.card_le_univ _

theorem paired_incidence_card {A V : Type*} [Fintype A] [Fintype V]
    (f g : A → V) (hinj : Function.Injective (fun a=>(f a,g a))) (v : V) :
    (Finset.univ.filter (fun a=>f a=v ∨ g a=v)).card≤2*Fintype.card V := by
  classical
  rw [Finset.filter_or]
  have h1 := paired_fiber_card f g hinj v
  have h2 := paired_fiber_card g f (fun a b he=>hinj (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))) v
  have hh := Finset.card_union_le (Finset.univ.filter (fun a=>f a=v)) (Finset.univ.filter (fun a=>g a=v))
  omega

theorem filter_card_sum_type {A B : Type*} [Fintype A] [Fintype B] (P : A⊕B → Prop) :
    (Finset.univ.filter P).card=(Finset.univ.filter (fun a=>P (Sum.inl a))).card+
      (Finset.univ.filter (fun b=>P (Sum.inr b))).card := by
  classical
  calc
    _ = ∑ x : A⊕B, if P x then (1:ℕ) else 0 := (Finset.sum_boole (R:=ℕ) P Finset.univ).symm
    _ = _ := by rw [Fintype.sum_sum_type]; simp only [Finset.sum_boole,Nat.cast_id]

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U]
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V) (H₀ Hₖ : V → U → Prop)

def markedResourceIncident (physical : Bool) : V⊕U → MarkedActiveEdge E K H₀ Hₖ → Prop
  | Sum.inl v,Sum.inl (Sum.inl e) => tail e=v ∨ head e=v
  | Sum.inl v,Sum.inl (Sum.inr e) => ktail e=v ∨ (if physical then π (khead e) else khead e)=v
  | Sum.inl v,Sum.inr vu => vu.val.1=v
  | Sum.inr _,Sum.inl _ => False
  | Sum.inr u,Sum.inr vu => vu.val.2=u

def markedIncidentEdges (physical : Bool) (x : V⊕U) : Finset (MarkedActiveEdge E K H₀ Hₖ) :=
  Finset.univ.filter (markedResourceIncident tail head ktail khead π H₀ Hₖ physical x)

theorem markedActiveEdge_card_bound
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Fintype.card (MarkedActiveEdge E K H₀ Hₖ)≤
      2*Fintype.card V^2+Fintype.card V*Fintype.card U := by
  have hi := markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  have hE := Fintype.card_le_of_injective (fun e=>(tail e,head e)) hi.1
  have hK := Fintype.card_le_of_injective (fun e=>(ktail e,khead e)) hi.2
  have hS := Fintype.card_subtype_le (fun vu : V×U=>H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2)
  simp only [Fintype.card_prod] at hE hK hS
  simp only [MarkedActiveEdge,Fintype.card_sum]
  nlinarith

theorem markedIncidentEdges_card_bound
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (physical : Bool) (x : V⊕U) :
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).card≤
      4*Fintype.card V+Fintype.card U := by
  have hi := markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  have hki : Function.Injective (fun e : K=>(ktail e,if physical then π (khead e) else khead e)) := by
    intro e f he
    apply hi.2
    refine Prod.ext ?_ ?_
    · exact (show ktail e=ktail f from congrArg (fun p : V×V=>p.1) he)
    · have hh := congrArg Prod.snd he
      cases physical with
      | false => exact hh
      | true => exact π.injective hh
  have hsi : Function.Injective (fun vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}=>(vu.val.1,vu.val.2)) :=
    fun a b he=>Subtype.ext he
  cases x with
  | inl v =>
    unfold markedIncidentEdges
    rw [filter_card_sum_type,filter_card_sum_type]
    simp only [markedResourceIncident]
    have hE := paired_incidence_card tail head hi.1 v
    have hK := paired_incidence_card ktail (fun e=>if physical then π (khead e) else khead e) hki v
    have hS := paired_fiber_card (fun vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}=>vu.val.1)
      (fun vu=>vu.val.2) hsi v
    have hh := Nat.add_le_add (Nat.add_le_add hE hK) hS
    have hr : 2*Fintype.card V+2*Fintype.card V+Fintype.card U=4*Fintype.card V+Fintype.card U := by omega
    rw [hr] at hh
    convert hh using 1 <;> congr!
  | inr u =>
    unfold markedIncidentEdges
    rw [filter_card_sum_type]
    simp only [markedResourceIncident,Finset.filter_false,Finset.card_empty,zero_add]
    have hS := paired_fiber_card (fun vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}=>vu.val.2)
      (fun vu=>vu.val.1) (fun a b he=>hsi (Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he))) u
    have hh := hS.trans (show Fintype.card V≤4*Fintype.card V+Fintype.card U by omega)
    convert hh using 1 <;> congr! 3

def markedPhysicalIncident : V⊕U → Finset V⊕(V×U) → Prop
  | Sum.inl v,Sum.inl e => v∈e
  | Sum.inl v,Sum.inr vu => vu.1=v
  | Sum.inr _,Sum.inl _ => False
  | Sum.inr u,Sum.inr vu => vu.2=u

theorem markedResourceIncident_physical (x : V⊕U) (e : MarkedActiveEdge E K H₀ Hₖ) :
    markedResourceIncident tail head ktail khead π H₀ Hₖ true x e ↔
      markedPhysicalIncident x (markedActivePhysical tail head ktail khead π H₀ Hₖ e) := by
  cases x with
  | inl v =>
    cases e with
    | inl e =>
      cases e <;> simp [markedResourceIncident,markedPhysicalIncident,markedActivePhysical,markedPhysicalEdge,eq_comm]
    | inr vu => rfl
  | inr u => cases e <;> rfl

theorem markedActiveResources_matching_physical {m b : ℕ}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedActiveResources W) (markedActiveResources Z)) :
    ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z) := by
  intro W hW Z hZ hne
  rw [← markedActiveResources_image W,← markedActiveResources_image Z]
  exact (Finset.disjoint_image (markedActivePhysical_injective hp)).mpr (hM W hW Z hZ hne)


def markedPhysicalIncidentEdges (x : V⊕U) : Finset (Finset V⊕(V×U)) :=
  (Finset.univ.image (markedActivePhysical tail head ktail khead π H₀ Hₖ)).filter (markedPhysicalIncident x)

theorem markedIncidentEdges_physical_image (x : V⊕U) :
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ true x).image
      (markedActivePhysical tail head ktail khead π H₀ Hₖ)=
      markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩,?_⟩
    exact (markedResourceIncident_physical tail head ktail khead π H₀ Hₖ x a).mp
      (Finset.mem_filter.mp ha).2
  · intro he
    obtain ⟨he,hi⟩ := Finset.mem_filter.mp he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact (markedResourceIncident_physical tail head ktail khead π H₀ Hₖ x a).mpr hi

theorem marked_leftover_card_physical {m b : ℕ}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (x : V⊕U) :
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ true x \ M.biUnion markedActiveResources).card=
      (markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \ M.biUnion markedWheelPhysicalResources).card := by
  have hh := Finset.card_image_of_injective
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ true x \ M.biUnion markedActiveResources)
    (markedActivePhysical_injective hp)
  rw [Finset.image_sdiff _ _ (markedActivePhysical_injective hp),
    markedIncidentEdges_physical_image,Finset.biUnion_image] at hh
  simp only [markedActiveResources_image] at hh
  exact hh.symm

end Oberwolfach
