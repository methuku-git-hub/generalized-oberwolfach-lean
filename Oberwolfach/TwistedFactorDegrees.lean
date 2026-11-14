module

public import Oberwolfach.PairEdgeDegree
public import Oberwolfach.MarkedPhysicalCycleProperties

@[expose] public section

/-! Physical heads in a marked factor. The ordinary head set must avoid
the successors of marked heads; the successor permutation stays ambient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [DecidableEq V] {m : ℕ}

def twistedTupleHead (π : Equiv.Perm V) (f : Fin (m+1) → V) : Fin (m+1) → V :=
  Fin.snoc (fun j => f j.succ) (π (f 0))

theorem twistedFactorHead_injective (π : Equiv.Perm V) (f : I → Fin (m+1) → V)
    (hf : Function.Injective (fun p : I×Fin (m+1) => f p.1 p.2))
    (hsep : ∀ i k (j : Fin m),f i j.succ≠π (f k 0)) :
    Function.Injective (fun p : I×Fin (m+1) => twistedTupleHead π (f p.1) p.2) := by
  rintro ⟨i,j⟩ ⟨k,l⟩
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun l => ?_) l
    · intro he
      simp only [twistedTupleHead,Fin.snoc_last,Fin.snoc_castSucc] at he
      have hh := hf (a₁:=(i,0)) (a₂:=(k,0)) (π.injective he)
      have hik : i=k := congrArg (fun p : I×Fin (m+1) => p.1) hh
      exact Prod.ext hik rfl
    · intro he
      simp only [twistedTupleHead,Fin.snoc_last,Fin.snoc_castSucc] at he
      exact (hsep k i l he.symm).elim
  · refine Fin.lastCases ?_ (fun l => ?_) l
    · intro he
      simp only [twistedTupleHead,Fin.snoc_last,Fin.snoc_castSucc] at he
      exact (hsep i k j he).elim
    · intro he
      simp only [twistedTupleHead,Fin.snoc_last,Fin.snoc_castSucc] at he
      have hh := hf (a₁:=(i,j.succ)) (a₂:=(k,l.succ)) he
      have hik : i=k := congrArg Prod.fst hh
      have hjl : j=l := Fin.succ_injective m (congrArg Prod.snd hh)
      subst k;subst l;rfl

theorem twisted_factor_incident_card (π : Equiv.Perm V) (f : I → Fin (m+1) → V)
    (hf : Function.Injective (fun p : I×Fin (m+1) => f p.1 p.2))
    (hsep : ∀ i k (j : Fin m),f i j.succ≠π (f k 0)) (v : V) :
    ((Finset.univ.image (fun p : I×Fin (m+1) =>
      ({f p.1 p.2,twistedTupleHead π (f p.1) p.2}:Finset V))).filter (fun e => v∈e)).card≤2 :=
  pair_edge_incident_card_le_two _ _ hf (twistedFactorHead_injective π f hf hsep) v

variable {E K : Type*} (tail head : E → V) (ktail khead : K → V)
    (π : Equiv.Perm V) (b : ℕ)

theorem markedCycle_physical_pair (C : MarkedCycleTuple tail head ktail khead m π b) (j : Fin (m+1)) :
    markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C j)=
      {C.val j,twistedTupleHead π C.val j} := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr,twistedTupleHead]
    have he := Classical.choose_spec C.property.2.2
    rw [he.1,he.2]
  · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl,twistedTupleHead]
    have he := Classical.choose_spec (C.property.2.1 j)
    rw [he.1,he.2]

end Oberwolfach
