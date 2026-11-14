module

public import Oberwolfach.MarkedMixedOutsideBalance

@[expose] public section
/-! Exact residual accounting: once the whole is divisible and the mixed
matching has the three vertex-local balances, divisibility of the remainder
is equivalent to the aggregate hub equation for that same matching. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T I:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop}

theorem marked_mixed_remainder_divisible_iff_hub_balance
    (m:ℕ) (A:Finset (E⊕T)) (S:Finset (V×U))
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (M:Finset I) (arc:I→Finset (E⊕T)) (spoke:I→Finset (V×U))
    (hArc:M.biUnion arc⊆A) (hSpoke:M.biUnion spoke⊆S)
    (hlocal:∀i∈M,MarkedFiniteLocalBalance (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (HK:=HK) (arc i) (spoke i))
    (hArcDis:∀i∈M,∀j∈M,i≠j→Disjoint (arc i) (arc j))
    (hSpokeDis:∀i∈M,∀j∈M,i≠j→Disjoint (spoke i) (spoke j)):
    MarkedRemainderDivisible tail head ktail khead HK (A\M.biUnion arc) (S\M.biUnion spoke) m ↔
    ∀u,((M.biUnion spoke).filter (fun s=>s.2=u∧¬HK s.1 s.2)).card=
      m*((M.biUnion spoke).filter (fun s=>s.2=u∧HK s.1 s.2)).card := by
  constructor
  · intro hrem
    have h := marked_finite_divisible_sdiff A (A\M.biUnion arc) S (S\M.biUnion spoke)
      Finset.sdiff_subset Finset.sdiff_subset hwhole hrem
    have ha:A\(A\M.biUnion arc)=M.biUnion arc := by
      ext a
      have hs:a∈M.biUnion arc→a∈A:=fun ha=>hArc ha
      simp only [Finset.mem_sdiff]
      tauto
    have hs:S\(S\M.biUnion spoke)=M.biUnion spoke := by
      ext a
      have ht:a∈M.biUnion spoke→a∈S:=fun ha=>hSpoke ha
      simp only [Finset.mem_sdiff]
      tauto
    rw [ha,hs] at h
    exact h.hub
  · intro hhub
    have hmatch:=marked_mixed_packing_finite_divisible m M arc spoke hlocal hArcDis hSpokeDis hhub
    exact marked_finite_divisible_sdiff A _ S _ hArc hSpoke hwhole hmatch
end Oberwolfach
