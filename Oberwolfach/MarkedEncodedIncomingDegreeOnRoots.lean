module

public import Oberwolfach.MarkedRestrictedDegreePhysicalOnRoots
public import Oberwolfach.MarkedEncodedHostIncomingDegree
public import Oberwolfach.MarkedRestrictedBalancePhysicalChanges

@[expose] public section
/-! The encoded corrected host's incoming degree differs from the original
sample by at most two physical change-graph degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K] [Fintype Γ] [Fintype Color]

theorem marked_encoded_host_incoming_degree_change_on_roots
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color)
    (tail head:E→V) (ktail khead:K→V)
    (hE:Function.Injective (fun e=>(tail e,head e)))
    (hK:Function.Injective (fun e=>(ktail e,khead e)))
    (hrim:∀mark x y,markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:K,ktail e=x∧khead e=y else ∃e:E,tail e=x∧head e=y)
    (FR:SimpleGraph V) (Roots:Finset V) (hRoots:∀x,x∈Roots→π x∈Roots) (η:ℝ)
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hFR:∀v∈Roots,(FR.degree v:ℝ)≤η):
    ∀v∈Roots,((Finset.univ.filter (fun a:E⊕K=>Sum.elim head khead a=v)).card:ℝ)-
      ((markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) false true v Finset.univ:ℝ)+
       (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) true true v Finset.univ:ℝ))≤2*η:=by
  intro v hv
  have hn:=marked_encoded_host_incoming_degree P π d τ tail head ktail khead hE hK hrim v
  have h0:=marked_restricted_degree_after_physical_changes_on_roots P π d Finset.univ σ τ FR η hchange Roots hRoots hFR false true v hv
  have h1:=marked_restricted_degree_after_physical_changes_on_roots P π d Finset.univ σ τ FR η hchange Roots hRoots hFR true true v hv
  linarith [(abs_le.mp h0).2,(abs_le.mp h1).2]
end Oberwolfach
