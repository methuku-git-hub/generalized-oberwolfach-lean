module

public import Oberwolfach.MarkedEncodedHostReservedRimTransfer

@[expose] public section
/-! Agreement of the actual physical rim states on a reserved resource set
implies the two type-specific transfers into the later encoded host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_rim_state_agreement_transfers
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E→V) (ktail khead:K→V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y)))
    (C:Finset (Finset V⊕(V×U)))
    (hstate:∀ e:Sym2 V,Sum.inl e.toFinset∈C→
      rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)=σ (Sum.inl e)):
    (∀ e:MarkedSampleArc P π (3*d) (fun f=>σ (Sum.inl f)) false,
      Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ a:E,tail a=e.val.1∧head a=e.val.2) ∧
    (∀ e:MarkedSampleArc P π (3*d) (fun f=>σ (Sum.inl f)) true,
      Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ a:K,ktail a=e.val.1∧khead a=e.val.2):=by
  constructor
  · intro e he
    have hs:=hstate s(e.val.1,e.val.2) (by simpa only [Sym2.toFinset_mk_eq] using he)
    have hh:markedPhysicalRim P π (3*d)
        (fun f=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl f)) false e.val.1 e.val.2=1:=by
      have heold:=e.property
      rw [markedPhysicalRim_eq_one_iff] at heold ⊢
      change ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 e.val.2 ∧
        rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl s(e.val.1,e.val.2))=
          some (false,orientationBit e.val.1 e.val.2)
      change ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 e.val.2 ∧
        σ (Sum.inl s(e.val.1,e.val.2))=some (false,orientationBit e.val.1 e.val.2) at heold
      exact ⟨heold.1,heold.2.1,hs.trans heold.2.2⟩
    simpa using (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false e.val.1 e.val.2).mp hh
  · intro e he
    have hs:=hstate s(e.val.1,π e.val.2) (by simpa only [Sym2.toFinset_mk_eq] using he)
    have hh:markedPhysicalRim P π (3*d)
        (fun f=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl f)) true e.val.1 e.val.2=1:=by
      have heold:=e.property
      rw [markedPhysicalRim_eq_one_iff] at heold ⊢
      change ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 (π e.val.2) ∧
        rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl s(e.val.1,π e.val.2))=
          some (true,orientationBit e.val.1 (π e.val.2))
      change ¬PermutationClose π (3*d) e.val.1 e.val.2 ∧ P.Adj e.val.1 (π e.val.2) ∧
        σ (Sum.inl s(e.val.1,π e.val.2))=some (true,orientationBit e.val.1 (π e.val.2)) at heold
      exact ⟨heold.1,heold.2.1,hs.trans heold.2.2⟩
    simpa using (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true e.val.1 e.val.2).mp hh
end Oberwolfach
