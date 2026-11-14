module

public import Oberwolfach.CanonicalMarkedPotentialLoads
public import Oberwolfach.ResourcePairImageBound

@[expose] public section

/-! Both spoke types are retained in potential resources. Forgetting the
spoke type is injective on each wheel, even when the parent spoke relations
overlap and the universe of physical rim images is not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

def typedMarkedOccurrenceResources
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : Finset ((E⊕K)⊕(Bool×V×U)) :=
  (Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)).image Sum.inl ∪
    Finset.univ.image (fun i=>Sum.inr (decide (i=0),W.1.val i,W.2.val))

def forgetMarkedSpokeType : ((E⊕K)⊕(Bool×V×U)) → ((E⊕K)⊕(V×U)) :=
  Sum.map id Prod.snd

theorem typedMarkedOccurrenceResources_rim
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : E⊕K) :
    Sum.inl e∈typedMarkedOccurrenceResources W ↔ CanonicalMarkedArcMem W.1 e := by
  simp [typedMarkedOccurrenceResources]

theorem typedMarkedOccurrenceResources_spoke
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (s : Bool×V×U) :
    Sum.inr s∈typedMarkedOccurrenceResources W ↔
      ∃ i,(decide (i=0),W.1.val i,W.2.val)=s := by
  simp only [typedMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,
    and_false,exists_false,false_or,Finset.mem_univ,true_and,Sum.inr.injEq]

theorem typedMarkedOccurrenceResources_forget_mem
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : (E⊕K)⊕(Bool×V×U))
    (he : e∈typedMarkedOccurrenceResources W) :
    forgetMarkedSpokeType e∈canonicalMarkedOccurrenceResources W := by
  cases e with
  | inl e =>
    rw [typedMarkedOccurrenceResources_rim] at he
    exact (canonicalMarkedOccurrenceResources_rim W e).mpr he
  | inr s =>
    obtain ⟨i,rfl⟩ := (typedMarkedOccurrenceResources_spoke W s).mp he
    change Sum.inr (W.1.val i,W.2.val)∈canonicalMarkedOccurrenceResources W
    rw [canonicalMarkedOccurrenceResources_spoke]
    exact ⟨rfl,i,rfl⟩

theorem typedMarkedOccurrenceResources_forget_inj
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (e f : (E⊕K)⊕(Bool×V×U))
    (he : e∈typedMarkedOccurrenceResources W) (hf : f∈typedMarkedOccurrenceResources W)
    (hef : forgetMarkedSpokeType e=forgetMarkedSpokeType f) : e=f := by
  cases e with
  | inl e =>
    cases f with
    | inl f => exact congrArg Sum.inl (Sum.inl.inj hef)
    | inr f => cases hef
  | inr e =>
    cases f with
    | inl f => cases hef
    | inr f =>
      obtain ⟨i,rfl⟩ := (typedMarkedOccurrenceResources_spoke W e).mp he
      obtain ⟨j,rfl⟩ := (typedMarkedOccurrenceResources_spoke W f).mp hf
      have hv : W.1.val i=W.1.val j := congrArg Prod.fst (Sum.inr.inj hef)
      have hij := permutationSeparated_injective π b W.1.val W.1.property.1 hv
      subst j
      rfl

theorem typedMarkedOmittedPair_le
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (hw : ∀ W,0≤w W)
    (e f : (E⊕K)⊕(Bool×V×U)) :
    resourceOmittedPairWeight typedMarkedOccurrenceResources w e f≤
      resourceOmittedPairWeight canonicalMarkedOccurrenceResources w
        (forgetMarkedSpokeType e) (forgetMarkedSpokeType f) :=
  resourceOmittedPairWeight_image_le typedMarkedOccurrenceResources canonicalMarkedOccurrenceResources
    forgetMarkedSpokeType typedMarkedOccurrenceResources_forget_mem
    (fun W e he f hf=>typedMarkedOccurrenceResources_forget_inj W e f he hf) w hw e f

def typedMarkedPotentialLoad (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (R : E⊕K → Prop) (H : Bool → V → U → Prop) (e : (E⊕K)⊕(Bool×V×U)) : ℝ :=
  resourceRootOmittedLoad typedMarkedOccurrenceResources w
    (Sum.elim R (fun jvu=>H jvu.1 jvu.2.1 jvu.2.2)) e

theorem typedMarkedPotentialLoad_change
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (hw : ∀ W,0≤w W)
    (R R' : E⊕K → Prop) (H H' : Bool → V → U → Prop) (e : (E⊕K)⊕(Bool×V×U)) :
    |typedMarkedPotentialLoad w R' H' e-typedMarkedPotentialLoad w R H e|≤
      (∑ f,if ¬(R f↔R' f) then resourceOmittedPairWeight typedMarkedOccurrenceResources w e (Sum.inl f) else 0)+
      (∑ j,∑ v,∑ u,if ¬(H j v u↔H' j v u) then resourceOmittedPairWeight typedMarkedOccurrenceResources w e (Sum.inr (j,v,u)) else 0) := by
  have hh := resourceRootOmittedLoad_change typedMarkedOccurrenceResources w hw
    (Sum.elim R (fun jvu : Bool×V×U=>H jvu.1 jvu.2.1 jvu.2.2))
    (Sum.elim R' (fun jvu : Bool×V×U=>H' jvu.1 jvu.2.1 jvu.2.2)) e
  simpa only [typedMarkedPotentialLoad,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type] using hh

end Oberwolfach
