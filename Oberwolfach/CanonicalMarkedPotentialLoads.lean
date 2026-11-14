module

public import Oberwolfach.CanonicalMarkedPairCosts
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section

/-! Marked potential loads on fixed parent occurrences and spoke pairs.
The tested root coordinate is omitted even when that root is absent. -/
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

def canonicalMarkedOccurrenceResources
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : Finset ((E⊕K)⊕(V×U)) :=
  (Finset.univ.filter (fun e=>CanonicalMarkedArcMem W.1 e)).image Sum.inl ∪
      Finset.univ.image (fun i=>Sum.inr (W.1.val i,W.2.val))

theorem canonicalMarkedOccurrenceResources_rim
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : E⊕K) :
    Sum.inl e∈canonicalMarkedOccurrenceResources W ↔ CanonicalMarkedArcMem W.1 e := by
  simp [canonicalMarkedOccurrenceResources]

theorem canonicalMarkedOccurrenceResources_spoke
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (v : V) (u : U) :
    Sum.inr (v,u)∈canonicalMarkedOccurrenceResources W ↔ W.2.val=u ∧ v∈Set.range W.1.val := by
  simp only [canonicalMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,
    and_false,exists_false,false_or,Finset.mem_univ,true_and,Sum.inr.injEq,Prod.mk.injEq,Set.mem_range]
  constructor
  · rintro ⟨i,hi,hu⟩;exact ⟨hu,i,hi⟩
  · rintro ⟨hu,i,hi⟩;exact ⟨i,hi,hu⟩

def canonicalMarkedPotentialLoad (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (R : E⊕K → Prop) (H : V → U → Prop) (e : (E⊕K)⊕(V×U)) : ℝ :=
  resourceRootOmittedLoad canonicalMarkedOccurrenceResources w (Sum.elim R (fun vu=>H vu.1 vu.2)) e

theorem canonicalMarkedOmittedPair_rims
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e f : E⊕K) :
    resourceOmittedPairWeight canonicalMarkedOccurrenceResources w (Sum.inl e) (Sum.inl f)=
      if e=f then 0 else canonicalMarkedRimPairWeight w e f := by
  unfold resourceOmittedPairWeight
  by_cases hef : e=f
  · subst f;simp
  · rw [if_neg hef]
    unfold canonicalMarkedRimPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp only [canonicalMarkedOccurrenceResources_rim,ne_eq,Sum.inl.injEq,Ne.symm hef,
      not_false_eq_true,and_true]

theorem canonicalMarkedOmittedPair_rim_spoke
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) (v : V) (u : U) :
    resourceOmittedPairWeight canonicalMarkedOccurrenceResources w (Sum.inl e) (Sum.inr (v,u))=
      canonicalMarkedRimSpokePairWeight w e v u := by
  unfold resourceOmittedPairWeight canonicalMarkedRimSpokePairWeight
  apply Finset.sum_congr rfl
  intro W _
  simp [canonicalMarkedOccurrenceResources_rim,canonicalMarkedOccurrenceResources_spoke, and_assoc]

theorem canonicalMarkedOmittedPair_spoke_rim
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) (v : V) (u : U) :
    resourceOmittedPairWeight canonicalMarkedOccurrenceResources w (Sum.inr (v,u)) (Sum.inl e)=
      canonicalMarkedRimSpokePairWeight w e v u := by
  unfold resourceOmittedPairWeight canonicalMarkedRimSpokePairWeight
  apply Finset.sum_congr rfl
  intro W _
  simp [canonicalMarkedOccurrenceResources_rim,canonicalMarkedOccurrenceResources_spoke, and_assoc, and_comm, and_left_comm]

theorem canonicalMarkedOmittedPair_spokes
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (v x : V) (u t : U) :
    resourceOmittedPairWeight canonicalMarkedOccurrenceResources w (Sum.inr (v,u)) (Sum.inr (x,t))=
      if (v,u)=(x,t) then 0 else markedSpokePairWeight w v x u t := by
  unfold resourceOmittedPairWeight
  by_cases hef : (v,u)=(x,t)
  · have hv : v=x := congrArg Prod.fst hef
    have hu : u=t := congrArg Prod.snd hef
    subst x;subst t;simp
  · rw [if_neg hef]
    unfold markedSpokePairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp only [canonicalMarkedOccurrenceResources_spoke,ne_eq,Sum.inr.injEq,Ne.symm hef,
      not_false_eq_true,and_true]

theorem canonicalMarkedPotentialLoad_change
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (hw : ∀ W,0≤w W)
    (R R' : E⊕K → Prop) (H H' : V → U → Prop) (e : (E⊕K)⊕(V×U)) :
    |canonicalMarkedPotentialLoad w R' H' e-canonicalMarkedPotentialLoad w R H e|≤
      (∑ f,if ¬(R f↔R' f) then resourceOmittedPairWeight canonicalMarkedOccurrenceResources w e (Sum.inl f) else 0)+
      (∑ v,∑ u,if ¬(H v u↔H' v u) then resourceOmittedPairWeight canonicalMarkedOccurrenceResources w e (Sum.inr (v,u)) else 0) := by
  have hh := resourceRootOmittedLoad_change canonicalMarkedOccurrenceResources w hw
    (Sum.elim R (fun vu : V×U=>H vu.1 vu.2)) (Sum.elim R' (fun vu : V×U=>H' vu.1 vu.2)) e
  simpa only [canonicalMarkedPotentialLoad,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Fintype.sum_prod_type] using hh

end Oberwolfach
