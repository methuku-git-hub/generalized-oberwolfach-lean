module

public import Oberwolfach.RawMarkedCandidateGeometry
public import Oberwolfach.OrdinaryCycleWeightRestriction
public import Oberwolfach.OrdinaryVertexTransfer

@[expose] public section

/-! Exact passage between the full pair-arc parent representation and
ordered tuples. Weights outside the prescribed separated support are zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem markedPairCycle_valid_iff (m b : ℕ) (π : Equiv.Perm V) (C : Fin (m+1)→V) :
    IsMarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b C ↔
      PermutationSeparated π b C := by
  refine ⟨fun h=>h.1,fun h=>⟨h,?_,?_⟩⟩
  · intro i;exact ⟨(C i.castSucc,C i.succ),rfl,rfl⟩
  · exact ⟨(C (Fin.last m),C 0),rfl,rfl⟩

theorem markedPairCycle_sum (m b : ℕ) (π : Equiv.Perm V)
    (f : (Fin (m+1)→V)→ℝ) (hf : ∀ C,¬PermutationSeparated π b C → f C=0) :
    (∑ C : MarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b,f C.val)=∑ C,f C := by
  symm
  apply finite_sum_restrict_of_zero
  intro C hC
  exact hf C (fun h=>hC ((markedPairCycle_valid_iff m b π C).mpr h))

theorem markedPairWheel_sum (m b : ℕ) (π : Equiv.Perm V)
    (f : (Fin (m+1)→V)→U→ℝ) (hf : ∀ C u,¬PermutationSeparated π b C → f C u=0) :
    (∑ W : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun _ _=>True) (fun _ _=>True),f W.1.val W.2.val)=∑ C,∑ u,f C u := by
  rw [Fintype.sum_sigma]
  trans ∑ C : MarkedCycleTuple (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π b,∑ u,f C.val u
  · apply Finset.sum_congr rfl
    intro C _
    symm
    apply finite_sum_restrict_of_zero
    intro u hu
    exact (hu ⟨trivial,fun _=>trivial⟩).elim
  · apply markedPairCycle_sum m b π (fun C=>∑ u,f C u)
    intro C hC
    exact Finset.sum_eq_zero (fun u _=>hf C u hC)

theorem typedMarkedSpoke_position_sum {E K : Type*} [Fintype E] [Fintype K]
    {tail head : E→V} {ktail khead : K→V} {m b : ℕ} {π : Equiv.Perm V} {H₀ Hₖ : V→U→Prop}
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (a : ℝ) (j : Bool) (v : V) (u : U) :
    (if Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W then a else 0)=
      ∑ i : Fin (m+1),if decide (i=0)=j ∧ W.1.val i=v ∧ W.2.val=u then a else 0 := by
  let f : Fin (m+1) ↪ Bool×V×U :=
    ⟨fun i=>(decide (i=0),W.1.val i,W.2.val),fun i k h=>
      permutationSeparated_injective π b W.1.val W.1.property.1
        (congrArg (fun z : Bool×V×U=>z.2.1) h)⟩
  have hi := injective_range_indicator f (j,v,u)
  have he : (j,v,u)∈Set.range f ↔ Sum.inr (j,v,u)∈typedMarkedOccurrenceResources W := by
    rw [typedMarkedOccurrenceResources_spoke]
    rfl
  have hh := congrArg (fun x : ℝ=>a*x) hi
  rw [Finset.mul_sum] at hh
  simp only [he] at hh
  simp only [f,Function.Embedding.coeFn_mk,Prod.mk.injEq] at hh
  convert hh.symm using 1 <;> simp only [mul_ite,mul_one,mul_zero]

theorem typedMarkedRim_position_sum {E K : Type*} [Fintype E] [Fintype K]
    {tail head : E→V} {ktail khead : K→V} {m b : ℕ} {π : Equiv.Perm V} {H₀ Hₖ : V→U→Prop}
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (a : ℝ) (e : E⊕K) :
    (if Sum.inl e∈typedMarkedOccurrenceResources W then a else 0)=
      ∑ i : Fin (m+1),if markedCycleTypedEdge tail head ktail khead m π b W.1 i=e then a else 0 := by
  let f : Fin (m+1) ↪ E⊕K :=
    ⟨markedCycleTypedEdge tail head ktail khead m π b W.1,
      markedCycleTypedEdge_injective tail head ktail khead m π b W.1⟩
  have hi := injective_range_indicator f e
  have he : e∈Set.range f ↔ Sum.inl e∈typedMarkedOccurrenceResources W := by
    rw [typedMarkedOccurrenceResources_rim]
    rfl
  have hh := congrArg (fun x : ℝ=>a*x) hi
  rw [Finset.mul_sum] at hh
  simp only [he] at hh
  simp only [f,Function.Embedding.coeFn_mk] at hh
  convert hh.symm using 1 <;> simp only [mul_ite,mul_one,mul_zero]

end Oberwolfach
