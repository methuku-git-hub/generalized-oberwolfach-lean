module

public import Oberwolfach.MarkedEndpointIndexEstimates

@[expose] public section

/-! Column estimates use one actual arc and one actual spoke. Their
error is measured against the original row domain, not its eligible subset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def markedEndpointLabels (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (A : Finset V) (a : Bool×Bool×V) (σ : RawMarkedOutcome V U Γ Color) : Finset V :=
  (markedRowDomain P π (3*d) A {a} ∅).filter (fun z=>rawMarkedPairRims P π d σ (markedRowRim a z))

theorem marked_endpoint_column_estimates
    (P : SimpleGraph V) (π : Equiv.Perm V) (d h : ℕ) (hh : 1≤h) (A : Finset V) (B : Finset U)
    (p k : ℝ) (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (err : ℝ) (herr : 0≤err)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hr : MarkedRowsWithSpokes P π d h A p k q s g j err σ H)
    (w : Bool→ℝ) (hq : ∀ u∈B,q u g=w true) (hs : ∀ u∈B,s u j=w false)
    (hw : ∀ t,0≤w t ∧ w t≤1) (a : Bool×Bool×V) :
    (|((markedEndpointLabels P π d A a σ).card:ℝ)-
      (if a.1 then k else p)*(markedRowDomain P π (3*d) A {a} ∅).card|≤err) ∧
    (∀ (t : Bool) u,u∈B →
      |(((markedEndpointLabels P π d A a σ).filter (fun z=>H t z u)).card:ℝ)-
        w t*(markedEndpointLabels P π d A a σ).card|≤2*err) := by
  let C := markedRowDomain P π (3*d) A {a} ∅
  let L := markedEndpointLabels P π d A a σ
  have hbase : |(L.card:ℝ)-(if a.1 then k else p)*C.card|≤err := by
    have he := hr {a} ∅ ∅ (by simpa using hh) (by simp) (by simp) (by simp)
    simpa [markedRowCountWithSpokes,markedEndpointLabels,L,C,Finset.card_filter,
      Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,-Finset.sum_boole] using he.le
  refine ⟨hbase,?_⟩
  intro t u hu
  have he := hr {a} ∅ {(t,u)} (by simpa using hh) (by simp) (by simpa using hh)
    (by intro b hb c hc he;simpa using (Finset.mem_singleton.mp hb).trans (Finset.mem_singleton.mp hc).symm)
  have hew : (if t then q u g else s u j)=w t := by
    cases t <;> simp [hq u hu,hs u hu]
  have he' : |((L.filter (fun z=>H t z u)).card:ℝ)-
      w t*((if a.1 then k else p)*C.card)|≤err := by
    simpa [markedRowCountWithSpokes,markedEndpointLabels,L,C,Finset.card_filter,
      Finset.filter_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,hew,mul_left_comm,mul_assoc,-Finset.sum_boole]
      using he.le
  exact count_error_after_comparing_target _ _ _ _ err (hw t).1 (hw t).2 herr he' hbase

theorem marked_endpoint_labels_separated
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (A : Finset V)
    (a : Bool×Bool×V) (σ : RawMarkedOutcome V U Γ Color) (z : V)
    (hz : z∈markedEndpointLabels P π d A a σ) :
    ¬PermutationClose π (3*d) a.2.2 z := by
  have hdom := (Finset.mem_filter.mp ((Finset.mem_filter.mp hz).1)).2
  exact (hdom.1 a (by simp)).1

end Oberwolfach
