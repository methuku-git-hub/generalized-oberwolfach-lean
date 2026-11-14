module

public import Oberwolfach.HypergraphColorClasses

@[expose] public section

/-! Indexed induced hypergraphs after vertex colouring, with an injective
projection to the original hyperedge indices and exact weight identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E I : Type} [Fintype V] [Fintype E] [Fintype I] [DecidableEq V] [Nonempty I]

abbrev MonochromaticHyperedge (R : E → Finset V) (σ : V → I) :=
  Σ i : I, {e : E // e∈hypergraphColorClass R σ i}

def monochromaticProjection (R : E → Finset V) (σ : V → I) (e : MonochromaticHyperedge R σ) : E := e.2.val

theorem monochromaticProjection_injective (R : E → Finset V) (σ : V → I)
    (hne : ∀ e,(R e).Nonempty) : Function.Injective (monochromaticProjection R σ) := by
  intro e f hef
  change e.2.val=f.2.val at hef
  obtain ⟨v,hv⟩ := hne e.2.val
  have hi : e.1=f.1 := by
    have he := (hypergraphColorClass_mem R σ e.1 e.2.val).mp e.2.property v hv
    have hf := (hypergraphColorClass_mem R σ f.1 f.2.val).mp f.2.property v (hef ▸ hv)
    exact he.symm.trans hf
  cases e with | mk i e =>
    cases f with | mk j f =>
      dsimp only at hi
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext hef)

theorem monochromatic_copies_disjoint (R : E → Finset V) (σ : V → I)
    (e f : MonochromaticHyperedge R σ) (hef : e.1≠f.1) :
    Disjoint (R (monochromaticProjection R σ e)) (R (monochromaticProjection R σ f)) :=
  hypergraphColorClass_disjoint_vertices R σ e.1 f.1 hef e.2.val f.2.val e.2.property f.2.property

theorem monochromatic_copies_part_sum (R : E → Finset V) (σ : V → I) (w : E → ℝ) (i : I) :
    (∑ e : MonochromaticHyperedge R σ,if e.1=i then w e.2.val else 0)=
      ∑ e∈hypergraphColorClass R σ i,w e := by
  classical
  rw [Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp only [ite_true]
    exact (Finset.sum_subtype (hypergraphColorClass R σ i) (fun e=>Iff.rfl) w).symm
  · intro j _ hji
    simp only [hji,ite_false,Finset.sum_const_zero]
  · simp

theorem monochromatic_copies_total_sum (R : E → Finset V) (σ : V → I) (w : E → ℝ) :
    (∑ e : MonochromaticHyperedge R σ,w e.2.val)=∑ i,∑ e∈hypergraphColorClass R σ i,w e := by
  classical
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sum_subtype (hypergraphColorClass R σ i) (fun e=>Iff.rfl) w).symm

theorem monochromatic_copies_part_count (R : E → Finset V) (σ : V → I)
    (P : E → Prop) (i : I) :
    (Finset.univ.filter (fun e : MonochromaticHyperedge R σ=>e.1=i ∧ P e.2.val)).card=
      ((hypergraphColorClass R σ i).filter P).card := by
  have hh := monochromatic_copies_part_sum R σ (fun e=>if P e then 1 else 0) i
  simp only [← ite_and,Finset.sum_boole] at hh
  exact_mod_cast hh

theorem monochromatic_copies_matching_projection (R : E → Finset V) (σ : V → I)
    (hne : ∀ e,(R e).Nonempty) (M : Finset (MonochromaticHyperedge R σ))
    (hM : ∀ e∈M,∀ f∈M,e≠f → Disjoint (R e.2.val) (R f.2.val)) :
    (∀ e∈M.image (monochromaticProjection R σ),∀ f∈M.image (monochromaticProjection R σ),
      e≠f → Disjoint (R e) (R f)) ∧
    (∀ w : E → ℝ,(∑ e∈M.image (monochromaticProjection R σ),w e)=∑ e∈M,w e.2.val) := by
  classical
  constructor
  · intro e he f hf hef
    obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f',hf',rfl⟩ := Finset.mem_image.mp hf
    exact hM e' he' f' hf' (fun h=>hef (congrArg (monochromaticProjection R σ) h))
  · intro w
    exact Finset.sum_image (fun e _ f _ h=>monochromaticProjection_injective R σ hne h)

end Oberwolfach
