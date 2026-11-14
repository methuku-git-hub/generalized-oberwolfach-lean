module

public import Oberwolfach.ProfileRootSampling

@[expose] public section

/-! Equality of the two concrete ways to count vertices in a class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem sigma_finset_class_card (A : Finset (Σ i,V i)) (i : I) :
    (A.filter (fun v => v.1=i)).card=
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card := by
  let f : {v : V i // (⟨i,v⟩ : Σ i,V i)∈A} → A.filter (fun v => v.1=i) :=
    fun v => ⟨⟨i,v.val⟩,Finset.mem_filter.mpr ⟨v.property,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro v w he
      apply Subtype.ext
      have hh : (⟨i,v.val⟩ : Σ i,V i)=⟨i,w.val⟩ := congrArg Subtype.val he
      exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2
    · rintro ⟨⟨j,v⟩,hv⟩
      have he : j=i := (Finset.mem_filter.mp hv).2
      subst j
      exact ⟨⟨v,(Finset.mem_filter.mp hv).1⟩,rfl⟩
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_subtype,Fintype.card_coe,Finset.filter_mem_eq_inter,Finset.univ_inter] using hh.symm

end Oberwolfach
