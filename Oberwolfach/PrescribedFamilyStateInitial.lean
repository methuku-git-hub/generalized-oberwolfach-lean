module

public import Oberwolfach.PrescribedFamilyState

@[expose] public section
/-! The initially prescribed maps and edges form a valid family state. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I X V:Type} [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_state_initial
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (R₀:I→Finset (Sym2 X)) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V) (t:ℝ)
    (ht:0≤t) (hinj:FamilyPartialInjections A₀ ψ) (hsubset:∀ i,A₀ i⊆QV i)
    (hsource:∀ i,R₀ i⊆(Q i).edgeFinset)
    (hends:∀ i e,e∈R₀ i→∀ x∈e.toFinset,x∈A₀ i)
    (hrepr:∀ i,E₀ i=(R₀ i).image (Sym2.map (ψ i)))
    (hpair:PairwisePhysicalDisjoint E₀):
    (PrescribedFamilyState.mk A₀ ψ ∅ R₀ E₀ (fun _=>∅)).Valid QV Q A₀ ψ E₀ J t := by
  refine ⟨hinj,?_,hsubset,?_,?_,hsource,hends,hrepr,hpair,?_,?_⟩
  · intro i x;simp
  · intro i x hx;rfl
  · intro v;simp;linarith
  · intro i;simp
  · intro i;simp
def prescribedInducedSourceEdges (Q:SimpleGraph X) (A:Finset X):Finset (Sym2 X):=
  Q.edgeFinset.filter (fun e=>∀ x∈e.toFinset,x∈A)

theorem prescribed_induced_family_state_initial
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V) (t:ℝ)
    (ht:0≤t) (hinj:FamilyPartialInjections A₀ ψ) (hsubset:∀ i,A₀ i⊆QV i)
    (hrepr:∀ i,E₀ i=(prescribedInducedSourceEdges (Q i) (A₀ i)).image (Sym2.map (ψ i)))
    (hpair:PairwisePhysicalDisjoint E₀):
    (PrescribedFamilyState.mk A₀ ψ ∅ (fun i=>prescribedInducedSourceEdges (Q i) (A₀ i)) E₀ (fun _=>∅)).Valid QV Q A₀ ψ E₀ J t := by
  apply prescribed_family_state_initial QV Q A₀ ψ _ E₀ J t ht hinj hsubset
  · intro i e he
    exact (Finset.mem_filter.mp he).1
  · intro i e he
    exact (Finset.mem_filter.mp he).2
  · exact hrepr
  · exact hpair
end Oberwolfach
