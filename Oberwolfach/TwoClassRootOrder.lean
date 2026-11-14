module

public import Oberwolfach.ProfileRootSampling
public import Oberwolfach.MarkedHubAbsorberAbundance

@[expose] public section

/-! Enumerate a root set with one marked-class vertex and m ordinary-class
vertices. This is an actual bijective enumeration, not an assumed ordering. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

def twoClassProfile (m : ℕ) (i : Bool) : ℕ := if i then 1 else m

variable {m : ℕ} {V : Bool → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem twoClassProfile_sum (m : ℕ) : ∑ i,twoClassProfile m i=m+1 := by
  simp [twoClassProfile,Nat.add_comm]

theorem exists_twoClass_root_order (σ : ∀ i,FixedSubset (V i) (twoClassProfile m i)) :
    ∃ x : Fin (m+1) → Σ i,V i,Function.Injective x ∧
      Finset.univ.image x=profileRootSet σ ∧
      (x 0).1=true ∧ ∀ j : Fin m,(x j.succ).1=false := by
  let eK : Fin 1 ≃ (σ true).val := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_coe,(σ true).property];rfl)
  let eO : Fin m ≃ (σ false).val := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,Fintype.card_coe,(σ false).property];rfl)
  let x : Fin (m+1) → Σ i,V i := Fin.cons (α:=fun _ => Σ i,V i)
    ⟨true,(eK 0).val⟩ (fun j => ⟨false,(eO j).val⟩)
  have hxi : Function.Injective x := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _;rfl
      · intro he
        have hh := congrArg Sigma.fst he
        exact Bool.noConfusion hh
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro he
        have hh := congrArg Sigma.fst he
        exact Bool.noConfusion hh
      · intro he
        have hv : (eO i).val=(eO j).val := (Sigma.mk.inj_iff.mp he).2 |> eq_of_heq
        exact congrArg Fin.succ (eO.injective (Subtype.ext hv))
  refine ⟨x,hxi,?_,rfl,fun _ => rfl⟩
  ext v
  constructor
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i,_,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (profileRootSet_mem σ true _).mpr (eK 0).property
    · exact (profileRootSet_mem σ false _).mpr (eO j).property
  · intro hv
    rcases v with ⟨i,v⟩
    cases i
    · let v' : (σ false).val := ⟨v,(profileRootSet_mem σ false v).mp hv⟩
      refine Finset.mem_image.mpr ⟨(eO.symm v').succ,Finset.mem_univ _,?_⟩
      change (⟨false,(eO (eO.symm v')).val⟩ : Σ i,V i)=⟨false,v⟩
      rw [Equiv.apply_symm_apply]
    · let v' : (σ true).val := ⟨v,(profileRootSet_mem σ true v).mp hv⟩
      have he : eK 0=v' := by
        have hz : eK.symm v'=0 := Subsingleton.elim _ _
        simpa only [hz] using eK.apply_symm_apply v'
      refine Finset.mem_image.mpr ⟨0,Finset.mem_univ _,?_⟩
      change (⟨true,(eK 0).val⟩ : Σ i,V i)=⟨true,v⟩
      rw [he]

end Oberwolfach
