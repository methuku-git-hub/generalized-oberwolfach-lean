module

public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! Adjoin the specified external root to each inner clique. The inner
edge set is unchanged, and distinct boundary stars cannot collide. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]

theorem complete_on_adj (S:Finset V) (x y:V):
    (spanningRestriction (⊤:SimpleGraph V) S).Adj x y↔x∈S ∧ y∈S ∧ x≠y:=by
  rw [spanningRestriction_adj,SimpleGraph.top_adj];tauto

theorem root_completed_cliques_disjoint (A S T:Finset V) (x y:V)
    (hSA:S⊆A) (hTA:T⊆A) (hx:x∉A) (hy:y∉A)
    (hinner:Disjoint (spanningRestriction (⊤:SimpleGraph V) S) (spanningRestriction ⊤ T))
    (hsame:x=y→Disjoint S T):
    Disjoint (spanningRestriction (⊤:SimpleGraph V) (insert x S))
      (spanningRestriction ⊤ (insert y T)):=by
  apply disjoint_iff_inf_le.mpr
  intro v w h
  obtain ⟨hv,hw,hvw⟩:=(complete_on_adj (insert x S) v w).mp h.1
  obtain ⟨hv',hw',_⟩:=(complete_on_adj (insert y T) v w).mp h.2
  simp only [Finset.mem_insert] at hv hw hv' hw'
  by_cases hva:v∈A
  · have hvs:v∈S:=hv.resolve_left (fun h=>hx (h ▸ hva))
    have hvt:v∈T:=hv'.resolve_left (fun h=>hy (h ▸ hva))
    by_cases hwa:w∈A
    · have hws:w∈S:=hw.resolve_left (fun h=>hx (h ▸ hwa))
      have hwt:w∈T:=hw'.resolve_left (fun h=>hy (h ▸ hwa))
      have hb:(⊥:SimpleGraph V).Adj v w:=(disjoint_iff_inf_le.mp hinner)
        ⟨(complete_on_adj S v w).mpr ⟨hvs,hws,hvw⟩,(complete_on_adj T v w).mpr ⟨hvt,hwt,hvw⟩⟩
      exact hb
    · have hwx:w=x:=hw.resolve_right (fun h=>hwa (hSA h))
      have hwy:w=y:=hw'.resolve_right (fun h=>hwa (hTA h))
      exact (Finset.disjoint_left.mp (hsame (hwx.symm.trans hwy)) hvs hvt).elim
  · have hvx:v=x:=hv.resolve_right (fun h=>hva (hSA h))
    have hvy:v=y:=hv'.resolve_right (fun h=>hva (hTA h))
    have hws:w∈S:=hw.resolve_left (fun h=>hvw (hvx.trans h.symm))
    have hwt:w∈T:=hw'.resolve_left (fun h=>hvw (hvy.trans h.symm))
    exact (Finset.disjoint_left.mp (hsame (hvx.symm.trans hvy)) hws hwt).elim

theorem root_completed_cliques_inner (A:Finset V) (x:I→V) (T:I→Finset V)
    (hx:∀ i,x i∉A) (hT:∀ i,T i⊆A):
    spanningRestriction (⨆ i,spanningRestriction (⊤:SimpleGraph V) (insert (x i) (T i))) A=
      ⨆ i,spanningRestriction (⊤:SimpleGraph V) (T i):=by
  ext v w
  rw [spanningRestriction_adj,SimpleGraph.iSup_adj,SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨⟨i,hi⟩,hv,hw⟩
    obtain ⟨hvi,hwi,hne⟩:=(complete_on_adj _ v w).mp hi
    simp only [Finset.mem_insert] at hvi hwi
    exact ⟨i,(complete_on_adj _ v w).mpr
      ⟨hvi.resolve_left (fun h=>hx i (h ▸ hv)),hwi.resolve_left (fun h=>hx i (h ▸ hw)),hne⟩⟩
  · rintro ⟨i,hi⟩
    obtain ⟨hvi,hwi,hne⟩:=(complete_on_adj _ v w).mp hi
    exact ⟨⟨i,(complete_on_adj _ v w).mpr
      ⟨Finset.mem_insert_of_mem hvi,Finset.mem_insert_of_mem hwi,hne⟩⟩,hT i hvi,hT i hwi⟩

theorem root_completed_cliques_at_root (A:Finset V) (x:I→V) (T:I→Finset V)
    (hx:∀ i,x i∉A) (hT:∀ i,T i⊆A) (z v:V) (hz:z∉A):
    (⨆ i,spanningRestriction (⊤:SimpleGraph V) (insert (x i) (T i))).Adj z v↔
      ∃ i,x i=z ∧ v∈T i:=by
  rw [SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨hzi,hvi,hne⟩:=(complete_on_adj _ z v).mp hi
    simp only [Finset.mem_insert] at hzi hvi
    have he:z=x i:=hzi.resolve_right (fun h=>hz (hT i h))
    exact ⟨i,he.symm,hvi.resolve_left (fun h=>hne (he.trans h.symm))⟩
  · rintro ⟨i,he,hv⟩
    exact ⟨i,(complete_on_adj _ z v).mpr
      ⟨by simp [he],Finset.mem_insert_of_mem hv,fun h=>hz (h ▸ hT i hv)⟩⟩

theorem root_completed_cliques_subgraph (G:SimpleGraph V) (x:I→V) (T:I→Finset V)
    (hT:∀ i,∀ v∈T i,∀ w∈T i,v≠w→G.Adj v w)
    (hx:∀ i,∀ v∈T i,G.Adj (x i) v):
    (⨆ i,spanningRestriction (⊤:SimpleGraph V) (insert (x i) (T i)))≤G:=by
  intro v w h
  obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp h
  obtain ⟨hv,hw,hne⟩:=(complete_on_adj _ v w).mp hi
  rcases Finset.mem_insert.mp hv with rfl|hv <;> rcases Finset.mem_insert.mp hw with rfl|hw
  · exact (hne rfl).elim
  · exact hx i w hw
  · exact (hx i v hv).symm
  · exact hT i v hv w hw hne

end Oberwolfach
