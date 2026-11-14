module

public import Oberwolfach.OrdinaryIsolatorCandidates
public import Oberwolfach.ExternalRootedDenseSets

@[expose] public section

/-! Lower counts for the actual potential isolator candidate family. Only
non-root vertices are required to lie in the sampled hub neighbourhood. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_isolator_candidate_many (α β : ℝ) (hα : 0<α) (hα1 : α≤1) (hβ : 0<β) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → ∃ c : ℝ,0<c ∧
    ∀ L : ℝ,0≤L → ∃ N : ℕ,∀ (V U : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (x y : V) (u : U),x≠y →
    ¬F.Adj x y → β*Fintype.card V≤(A.card:ℝ) → (∀ z∈A,H z u) →
    ∀ θ : ℝ,0≤θ → θ≤1 →
    (∀ v∈A∪{x,y},(θ+α/2)*(A.card:ℝ)≤((P.neighborFinset v∩A).card:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    c*(Fintype.card V:ℝ)^k≤Fintype.card (OrdinaryIsolatorCandidate P F H (2+k) θ (α/4) x y u) := by
  obtain ⟨K,hK⟩ := external_rooted_dense_sets 2 α β hα hα1 hβ
  refine ⟨K,?_⟩
  intro k hk
  obtain ⟨c,hc,hcN⟩ := hK k hk
  refine ⟨c,hc,?_⟩
  intro L hL
  obtain ⟨N,hN⟩ := hcN L hL
  refine ⟨N,?_⟩
  intro V U _ _ hn P F H A x y u hxy hFxy hA hH θ hθ hθ1 hP hF
  have hrootcard : ({x,y}:Finset V).card=2 := by simp [hxy]
  have hind : ∀ z∈({x,y}:Finset V),∀ t∈({x,y}:Finset V),¬F.Adj z t := by
    intro z hz t ht
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz ht
    rcases hz with rfl|rfl <;> rcases ht with rfl|rfl
    · exact F.loopless.irrefl _
    · exact hFxy
    · exact fun h=>hFxy h.symm
    · exact F.loopless.irrefl _
  have hh := hN V hn P F A {x,y} hrootcard hA θ hθ hθ1 hP hF hind
  let Good := {S : FixedSubset V (2+k) // ({x,y}:Finset V)⊆S.val ∧ S.val⊆A∪{x,y} ∧
    (∀ v∈S.val,(θ+α/4)*(2+k:ℝ)≤((P.neighborFinset v∩S.val).card:ℝ)) ∧
    (∀ z∈S.val,∀ t∈S.val,¬F.Adj z t)}
  let f (S : Good) : OrdinaryIsolatorCandidate P F H (2+k) θ (α/4) x y u :=
    ⟨S.val,⟨S.property.1 (by simp),S.property.1 (by simp)⟩,
      (by
        intro z hz hzx hzy
        have ha := S.property.2.1 hz
        have ha' : z∈A := by
          simpa only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,hzx,hzy,
            false_or,or_false] using ha
        exact hH z ha'),
      S.property.2.2.2,(by simpa only [Nat.cast_add,Nat.cast_ofNat] using S.property.2.2.1)⟩
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    exact congrArg (fun a : OrdinaryIsolatorCandidate P F H (2+k) θ (α/4) x y u=>a.val) he
  have hcard : (Fintype.card Good:ℝ)≤Fintype.card (OrdinaryIsolatorCandidate P F H (2+k) θ (α/4) x y u) := by
    exact_mod_cast Fintype.card_le_of_injective f hinj
  exact hh.trans hcard

end Oberwolfach
