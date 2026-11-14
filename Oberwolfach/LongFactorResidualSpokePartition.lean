module

public import Oberwolfach.LongFactorProvenanceRoots
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! Partition the residual spoke set into ordinary spokes and the actual
retained marked spokes, using the same factor-complement witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance factorResidualSpokeFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_factor_residual_spoke_partition
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (S P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F S P π d m raw t Jret Pack Enew A R):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
    let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false true true
    (∀w x,HK x w↔x∈Y w) ∧
    (∀w x,x∈R w↔x∈R w\Y w∨HK x w) ∧
    (∀w x,HK x w→x∉R w\Y w):=by
  intro Y HK
  have hsubset:=long_factor_provenance_roots_subset F S P π d m hd hnoshort raw t Jret Pack Enew A R hprov
  have hmarked:∀w x,HK x w↔x∈Y w:=by
    intro w x
    exact (retained_marked_root_membership π d (by omega) (fun e=>raw (Sum.inr e)) false t Jret w x).symm
  refine ⟨hmarked,?_,?_⟩
  · intro w x
    rw [hmarked]
    simp only [Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hy:x∈Y w
      · exact Or.inr hy
      · exact Or.inl ⟨hx,hy⟩
    · rintro (⟨hx,_⟩|hy)
      · exact hx
      · exact hsubset w hy
  · intro w x hx
    rw [hmarked] at hx
    simp only [Finset.mem_sdiff,not_and]
    intro _
    exact fun h=>h hx
end Oberwolfach
