module

public import Oberwolfach.OrdinaryLocalPairAgreement
public import Oberwolfach.OrdinaryBoundaryBalanceProfiles

@[expose] public section
/-! Exact protected-pair agreement preserves the rim and spoke counts used
for inner and cross-boundary balance on every smaller pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_pair_balance_agreement
    (R G:SimpleGraph V) (J H:V→U→Prop) (Inner Parent I:Finset V) (Hubs B:Finset U)
    (hParent:Parent⊆Inner) (hI:I⊆Parent) (hB:B⊆Hubs)
    (hr:∀v∈Inner,∀w∈Inner,R.Adj v w↔G.Adj v w)
    (hs:∀v∈Inner,∀u∈Hubs,J v u↔H v u):
    spanningRestriction R I=spanningRestriction G I ∧
    (∀v∈Parent,R.neighborFinset v∩I=G.neighborFinset v∩I) ∧
    (∀v∈Parent,B.filter (J v)=B.filter (H v)) ∧
    (∀v∈Parent,Finset.univ.filter (fun u=>J v u∧v∈I∧u∈B)=
      Finset.univ.filter (fun u=>H v u∧v∈I∧u∈B)) :=by
  have hI':I⊆Inner:=hI.trans hParent
  refine ⟨?_,?_,?_,?_⟩
  · ext v w
    simp only [spanningRestriction_adj]
    by_cases hv:v∈I <;> by_cases hw:w∈I
    · simpa [hv,hw] using hr v (hI' hv) w (hI' hw)
    · simp [hw]
    · simp [hv]
    · simp [hv]
  · intro v hv
    ext w
    simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    by_cases hw:w∈I
    · simpa [hw] using hr v (hParent hv) w (hI' hw)
    · simp [hw]
  · intro v hv
    ext u
    simp only [Finset.mem_filter]
    by_cases hu:u∈B
    · simpa [hu] using hs v (hParent hv) u (hB hu)
    · simp [hu]
  · intro v hv
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hu:u∈B
    · have hh:=hs v (hParent hv) u (hB hu)
      tauto
    · simp [hu]
end Oberwolfach
