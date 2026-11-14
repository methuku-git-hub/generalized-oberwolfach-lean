module

public import Oberwolfach.LongUnusedOrdinarySpokeFromMatching

@[expose] public section
/-! Every true ordinary label is occupied or belongs to the unused set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_unused_ordinary_spokes_cover
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (old:U→Finset (Fin n)):
    ∀w v,rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w)=some (Sum.inr true)→
      v∈old w ∨ v∈longUnusedOrdinarySpokes π d raw old w:=by
  intro w v hv
  by_cases h:v∈old w
  · exact Or.inl h
  · right
    simp only [longUnusedOrdinarySpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · simp only [rawMarkedPairSpokes,rawMarkedSpokes]
      convert hv using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
    · exact h
end Oberwolfach
