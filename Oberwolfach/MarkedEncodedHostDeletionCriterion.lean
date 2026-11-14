module

public import Oberwolfach.MarkedHostRawEncoding
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section

/-! An exact coordinate criterion for representing an encoded typed host
as a raw rim deletion. This is a finite-set deletion criterion; degree
and looplessness requirements for a physical deletion graph remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem encoded_host_rim_deletion_iff
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V):
    (∃ D:Finset (Sym2 V),rawMarkedEncodeHost tail head ktail khead π σ I=rawMarkedDeleteRims σ D) ↔
    (∀ e:Sym2 V,¬e.toFinset⊆I→
      markedHostRimEncoding tail head ktail khead π e=none ∨
      markedHostRimEncoding tail head ktail khead π e=σ (Sum.inl e)) := by
  classical
  constructor
  · rintro ⟨D,hD⟩ e hout
    have hh:=congrFun hD (Sum.inl e)
    rw [rawMarkedEncodeHost,ite_eq_right hout,rawMarkedDeleteRims] at hh
    by_cases he:e∈D
    · left;simpa [he] using hh
    · right;simpa [he] using hh
  · intro hcomp
    let D:Finset (Sym2 V):=Finset.univ.filter (fun e=>¬e.toFinset⊆I ∧
      markedHostRimEncoding tail head ktail khead π e=none)
    refine ⟨D,?_⟩
    funext a
    cases a with
    | inr z=>rfl
    | inl e=>
      simp only [rawMarkedEncodeHost,rawMarkedDeleteRims,D,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.subset_iff,Sym2.mem_toFinset]
      have hc:=hcomp e
      simp only [Finset.subset_iff,Sym2.mem_toFinset] at hc
      by_cases hi:∀ ⦃x:V⦄,x∈e→x∈I
      · split_ifs <;> simp_all
      · by_cases he:markedHostRimEncoding tail head ktail khead π e=none
        · simp [hi,he]
        · have hs:= (hc hi).resolve_left he
          simp [hi,he,hs]
end Oberwolfach
