module

public import Oberwolfach.OrdinaryLocalExtensions

@[expose] public section

/-! Restricting the original extension counts to later free vertex sets.
The lost candidates are counted on the original fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem common_domain_restriction_card {T:Type*} [DecidableEq T]
    (A X:Finset T) (p:T→Prop) [DecidablePred p]:
    (A.filter p).card≤(X.filter p).card+(A\X).card:=by
  have hs:A.filter p⊆X.filter p∪(A\X):=by
    intro a ha
    by_cases hx:a∈X
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,(Finset.mem_filter.mp ha).2⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp ha).1,hx⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

theorem prescribed_edge_extension_counts (Q F:SimpleGraph V) (H:V→U→Prop)
    (A X:Finset V) (U₀ B:Finset U) (β:ℝ)
    (hXA:((A\X).card:ℝ)≤β*A.card/2) (hBU:((U₀\B).card:ℝ)≤β*U₀.card/2)
    (hrows:∀ S:Finset V,∀ J:Finset U,S.card≤2 → J.card≤1 →
      β*A.card≤((common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ))
    (hindices:∀ S:Finset V,S.card≤2 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      β*U₀.card≤((common U₀ S (fun v=>Finset.univ.filter (H v))).card:ℝ)) :
    (∀ u a c,β*A.card/2≤(((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) ∧
    (∀ a c,¬F.Adj a c → β*U₀.card/2≤((B.filter (fun u=>H a u∧H c u)).card:ℝ)) :=by
  constructor
  · intro u a c
    have he (Z:Finset V):common (common Z ({a,c}:Finset V) (fun v=>Q.neighborFinset v)) ({u}:Finset U)
        (fun u=>Finset.univ.filter (fun v=>H v u))=Z.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v):=by
      ext v;simp [mem_common_iff];tauto
    have he' (Z:Finset V):Z.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)=
        (Z.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c:=by
      ext v;simp;tauto
    have hh:=hrows {a,c} {u} Finset.card_le_two (by simp)
    rw [he] at hh
    have hc:((A.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)).card:ℝ)≤
      (X.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)).card+(A\X).card:=by
      exact_mod_cast common_domain_restriction_card A X (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)
    rw [he' X] at hc
    linarith only [hh,hc,hXA]
  · intro a c hfac
    have hsep:∀ v∈({a,c}:Finset V),∀ w∈({a,c}:Finset V),¬F.Adj v w:=by
      intro v hv w hw h
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
      · exact F.loopless.irrefl _ h
      · exact hfac h
      · exact hfac h.symm
      · exact F.loopless.irrefl _ h
    have he:common U₀ ({a,c}:Finset V) (fun v=>Finset.univ.filter (H v))=
        U₀.filter (fun u=>H a u∧H c u):=by ext u;simp [mem_common_iff]
    have hh:=hindices {a,c} Finset.card_le_two hsep
    rw [he] at hh
    have hc:((U₀.filter (fun u=>H a u∧H c u)).card:ℝ)≤
      (B.filter (fun u=>H a u∧H c u)).card+(U₀\B).card:=by
      exact_mod_cast common_domain_restriction_card U₀ B (fun u=>H a u∧H c u)
    linarith only [hh,hc,hBU]

end Oberwolfach
