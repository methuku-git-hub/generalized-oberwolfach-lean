module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! The incidence conclusions of protected cover-down imply the concrete
arc, row and hub counts used by the next balance and deletion arguments.
Physical marked heads remain at their successor images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_counts_from_incidence
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H₀ HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (B : Finset (Finset V⊕(V×U))) (δ : ℝ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈S,H₀ s.1 s.2 ∨ HK s.1 s.2)
    (hSB : ∀ s∈S,Sum.inr s∈B)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B)).card : ℝ)≤δ) :
    (∀ v,((A.filter (fun a=>Sum.elim tail ktail a=v ∨ Sum.elim head khead a=v)).card : ℝ)≤δ) ∧
    (∀ v,((S.filter (fun s=>s.1=v)).card : ℝ)≤δ) ∧
    (∀ u,((S.filter (fun s=>s.2=u)).card : ℝ)≤δ) ∧
    (∀ v,((A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card : ℝ)≤δ) := by
  have arc (physical : Bool) (z : V⊕U) (q : E⊕K→Prop) [DecidablePred q]
      (hq : ∀ a∈A,q a→markedResourceIncident tail head ktail khead π H₀ HK physical z (Sum.inl a)) :
      ((A.filter q).card : ℝ)≤δ := by
    apply le_trans _ (hB physical z)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card_of_injOn (Sum.inl : E⊕K→MarkedActiveEdge E K H₀ HK)
    · intro a ha
      obtain ⟨ha,hq'⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq a ha hq'⟩,hA a ha⟩
    · intro a ha b hb hab
      exact Sum.inl.inj hab
  have spoke (z : V⊕U) (q : V×U→Prop) [DecidablePred q]
      (hq : ∀ s∈S,∀ hs : H₀ s.1 s.2 ∨ HK s.1 s.2,q s→
        markedResourceIncident tail head ktail khead π H₀ HK false z (Sum.inr ⟨s,hs⟩)) :
      ((S.filter q).card : ℝ)≤δ := by
    let T := S.filter q
    let f : T→MarkedActiveEdge E K H₀ HK := fun s=>Sum.inr ⟨s.val,hS s.val (Finset.mem_filter.mp s.property).1⟩
    have hinj : Function.Injective f := by
      intro a b h
      dsimp [f] at h
      have hh := Sum.inr.inj h
      exact Subtype.ext (congrArg (fun s : {s : V×U // H₀ s.1 s.2 ∨ HK s.1 s.2}=>s.val) hh)
    have hc : T.card≤((markedIncidentEdges tail head ktail khead π H₀ HK false z).filter
        (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B)).card := by
      rw [← Fintype.card_coe T,← Finset.card_univ (α:=T)]
      apply Finset.card_le_card_of_injOn f
      · intro s _
        obtain ⟨hs,hq'⟩ := Finset.mem_filter.mp s.property
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hq s.val hs _ hq'⟩,hSB s.val hs⟩
      · intro a ha b hb hab
        exact hinj hab
    exact (Nat.cast_le.mpr hc).trans (hB false z)
  refine ⟨?_,?_,?_,?_⟩
  · intro v
    apply arc false (Sum.inl v) (fun a=>Sum.elim tail ktail a=v ∨ Sum.elim head khead a=v)
    intro a ha h
    cases a <;> exact h
  · intro v
    apply spoke (Sum.inl v) (fun s=>s.1=v)
    intro s hs ht h
    exact h
  · intro u
    apply spoke (Sum.inr u) (fun s=>s.2=u)
    intro s hs ht h
    exact h
  · intro v
    apply arc true (Sum.inl v) (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)
    intro a ha h
    exact (markedResourceIncident_physical tail head ktail khead π H₀ HK (Sum.inl v) (Sum.inl a)).mpr h

theorem marked_finite_star_counts_from_incidence
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H₀ HK : V→U→Prop)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (B : Finset (Finset V⊕(V×U)))
    (X : Finset V) (Z : Finset U) (hX : ∀ v,π v∈X↔v∈X) (δ : ℝ)
    (hA : ∀ a∈A,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B)
    (hS : ∀ s∈S,H₀ s.1 s.2 ∨ HK s.1 s.2) (hSB : ∀ s∈S,Sum.inr s∈B)
    (hB : ∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∈B.filter (markedStarResource X Z))).card : ℝ)≤δ) :
    let EA := A.filter (fun a=>Sum.elim tail ktail a∈X ∨ Sum.elim head khead a∈X)
    let ES := S.filter (fun s=>s.1∈X ∨ s.2∈Z);
    (∀ v,((EA.filter (fun a=>Sum.elim tail ktail a=v ∨ Sum.elim head khead a=v)).card : ℝ)≤δ) ∧
    (∀ v,((ES.filter (fun s=>s.1=v)).card : ℝ)≤δ) ∧
    (∀ u,((ES.filter (fun s=>s.2=u)).card : ℝ)≤δ) ∧
    (∀ v,((EA.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card : ℝ)≤δ) := by
  intro EA ES
  apply marked_finite_counts_from_incidence tail head ktail khead π H₀ HK EA ES _ δ _ _ _ hB
  · intro a ha
    obtain ⟨ha,hx⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨hA a ha,(marked_physical_rim_star_iff tail head ktail khead π X Z hX a).mpr hx⟩
  · intro s hs
    exact hS s (Finset.mem_filter.mp hs).1
  · intro s hs
    obtain ⟨hs,hx⟩ := Finset.mem_filter.mp hs
    exact Finset.mem_filter.mpr ⟨hSB s hs,hx⟩

end Oberwolfach
