module

public import Oberwolfach.MarkedCommonSubhostAgreement
public import Oberwolfach.MarkedHostRawEncoding

@[expose] public section
/-! Replacing the original sample by a physical rim deletion that avoids
the protected row set does not change the encoded later host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_encode_after_protected_rim_deletion
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (D:SimpleGraph V)
    (hinner:∀ x∈I,∀ y∈I,¬D.Adj x y):
    rawMarkedEncodeHost tail head ktail khead π (rawMarkedDeleteRims σ D.edgeFinset) I =
      rawMarkedEncodeHost tail head ktail khead π σ I :=by
  funext a
  cases a with
  | inr z=>rfl
  | inl e=>
    induction e using Sym2.ind with
    | _ x y=>
      by_cases hin:x∈I∧y∈I
      · have hn:s(x,y)∉D.edgeFinset:=by
          intro he
          exact hinner x hin.1 y hin.2 (SimpleGraph.mem_edgeFinset.mp he)
        simp only [rawMarkedEncodeHost,Sym2.toFinset_mk_eq,Finset.insert_subset_iff,
          Finset.singleton_subset_iff,hin,ite_true,rawMarkedDeleteRims,hn,ite_false]
      · simp only [rawMarkedEncodeHost,Sym2.toFinset_mk_eq,Finset.insert_subset_iff,
          Finset.singleton_subset_iff,hin,ite_false]
end Oberwolfach
