module

public import Oberwolfach.FreshBipartitePhysicalEvent

@[expose] public section

/-! Independent physical sampling on the actual root domains. Auxiliary
coins extend an injective partial coordinate map only for the projection
argument; the resulting event uses exactly the original physical coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E : Type} [DecidableEq V]

def partialPhysicalEmbedding (S : Finset V) (f : V→E)
    (hf : Set.InjOn f (S:Set V)) : V↪E⊕V where
  toFun v := if v∈S then Sum.inl (f v) else Sum.inr v
  inj' := by
    intro v w h
    by_cases hv:v∈S <;> by_cases hw:w∈S <;> simp only [hv,hw,ite_true,ite_false] at h
    · exact hf hv hw (Sum.inl.inj h)
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · exact Sum.inr.inj h

theorem partial_physical_filter (S A : Finset V) (hA : A⊆S) (f : V→E)
    (hf : Set.InjOn f (S:Set V)) (σ : E⊕V→Bool) :
    A.filter (fun v=>σ (partialPhysicalEmbedding S f hf v)=true)=
      A.filter (fun v=>σ (Sum.inl (f v))=true) := by
  apply Finset.filter_congr
  intro v hv
  change σ (if v∈S then Sum.inl (f v) else Sum.inr v)=true ↔ _
  rw [if_pos (hA hv)]

end Oberwolfach
