module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
/-! A realized forbidden or deleted arc is charged once at its head. No
sampling density is applied to the deterministic loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype E]

theorem incoming_candidate_loss (head:E→V) (S T B:Finset E) (v:V)
    (h:S\T⊆B) :
    (S.filter (fun e=>head e=v)).card ≤
      (T.filter (fun e=>head e=v)).card + (B.filter (fun e=>head e=v)).card := by
  have hsub : S.filter (fun e=>head e=v) ⊆
      T.filter (fun e=>head e=v) ∪ B.filter (fun e=>head e=v) := by
    intro e he
    obtain ⟨he,hv⟩ := Finset.mem_filter.mp he
    by_cases ht:e∈T
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ht,hv⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h (Finset.mem_sdiff.mpr ⟨he,ht⟩),hv⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem incoming_forbidden_union_loss (head:E→V) (S B₁ B₂ B₃:Finset E) (v:V) :
    (S.filter (fun e=>head e=v)).card ≤
      ((S\(B₁∪B₂∪B₃)).filter (fun e=>head e=v)).card +
      (B₁.filter (fun e=>head e=v)).card + (B₂.filter (fun e=>head e=v)).card +
      (B₃.filter (fun e=>head e=v)).card := by
  have hbase := incoming_candidate_loss head S (S\(B₁∪B₂∪B₃)) (B₁∪B₂∪B₃) v (by
    intro e he
    have hh := Finset.mem_sdiff.mp he
    by_contra hn
    exact hh.2 (Finset.mem_sdiff.mpr ⟨hh.1,hn⟩))
  have hfilter : ((B₁∪B₂∪B₃).filter (fun e=>head e=v)) =
      (B₁.filter (fun e=>head e=v)) ∪ (B₂.filter (fun e=>head e=v)) ∪
        (B₃.filter (fun e=>head e=v)) := by
    ext e
    simp only [Finset.mem_filter,Finset.mem_union]
    tauto
  rw [hfilter] at hbase
  have h12 := Finset.card_union_le (B₁.filter (fun e=>head e=v)) (B₂.filter (fun e=>head e=v))
  have h123 := Finset.card_union_le ((B₁.filter (fun e=>head e=v)) ∪ (B₂.filter (fun e=>head e=v)))
    (B₃.filter (fun e=>head e=v))
  omega
theorem incoming_tail_domain_card_le (tail head:E→V) (I:Finset V) (v:V)
    (hpair:Function.Injective (fun e:E=>(tail e,head e))) :
    (Finset.univ.filter (fun e=>head e=v ∧ tail e∈I)).card≤I.card := by
  apply Finset.card_le_card_of_injOn tail
  · intro e he
    exact (Finset.mem_filter.mp he).2.2
  · intro e he e' he' htail
    apply hpair
    apply Prod.ext
    · exact htail
    · exact (Finset.mem_filter.mp he).2.1.trans (Finset.mem_filter.mp he').2.1.symm
theorem incoming_flexible_type_availability
    (head:E→V) (S₀ S₁ T₀ T₁ B₀ B₁ F:Finset E) (v:V)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁) :
    let A:=(T₀∪T₁)\F
    (S₁.filter (fun e=>head e=v)).card ≤
      ((A∩T₁).filter (fun e=>head e=v)).card +
      (B₁.filter (fun e=>head e=v)).card + (F.filter (fun e=>head e=v)).card ∧
    (S₀.filter (fun e=>head e=v)).card ≤
      ((A\T₁).filter (fun e=>head e=v)).card +
      (B₀.filter (fun e=>head e=v)).card + (F.filter (fun e=>head e=v)).card := by
  intro A
  have hmark : A∩T₁=T₁\F := by
    ext e
    simp only [A,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_union]
    tauto
  have hord : A\T₁=T₀\F := by
    ext e
    simp only [A,Finset.mem_sdiff,Finset.mem_union]
    have hd : ¬(e∈T₀ ∧ e∈T₁) := fun h=>Finset.disjoint_left.mp hdis h.1 h.2
    tauto
  have hF₁ : T₁\(T₁\F)⊆F := by
    intro e he
    simp only [Finset.mem_sdiff] at he
    by_contra hn
    exact he.2 ⟨he.1,hn⟩
  have hF₀ : T₀\(T₀\F)⊆F := by
    intro e he
    simp only [Finset.mem_sdiff] at he
    by_contra hn
    exact he.2 ⟨he.1,hn⟩
  have hS₁:=incoming_candidate_loss head S₁ T₁ B₁ v h₁
  have hT₁:=incoming_candidate_loss head T₁ (T₁\F) F v hF₁
  have hS₀:=incoming_candidate_loss head S₀ T₀ B₀ v h₀
  have hT₀:=incoming_candidate_loss head T₀ (T₀\F) F v hF₀
  rw [hmark,hord]
  omega
theorem incoming_flexible_availability_real
    (head:E→V) (S₀ S₁ T₀ T₁ B₀ B₁ F:Finset E) (v:V)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁)
    (base₀ base₁ loss₀ loss₁ forbid threshold:ℝ)
    (hbase₀:base₀≤(S₀.filter (fun e=>head e=v)).card)
    (hbase₁:base₁≤(S₁.filter (fun e=>head e=v)).card)
    (hloss₀:((B₀.filter (fun e=>head e=v)).card:ℝ)≤loss₀)
    (hloss₁:((B₁.filter (fun e=>head e=v)).card:ℝ)≤loss₁)
    (hforbid:((F.filter (fun e=>head e=v)).card:ℝ)≤forbid)
    (hmargin₀:threshold≤base₀-loss₀-forbid) (hmargin₁:threshold≤base₁-loss₁-forbid) :
    let A:=(T₀∪T₁)\F
    threshold≤((A∩T₁).filter (fun e=>head e=v)).card ∧
    threshold≤((A\T₁).filter (fun e=>head e=v)).card := by
  intro A
  obtain ⟨h₁,h₀⟩ := incoming_flexible_type_availability head S₀ S₁ T₀ T₁ B₀ B₁ F v hdis h₀ h₁
  have hr₁ : ((S₁.filter (fun e=>head e=v)).card:ℝ) ≤
      ((A∩T₁).filter (fun e=>head e=v)).card +
      (B₁.filter (fun e=>head e=v)).card + (F.filter (fun e=>head e=v)).card := by exact_mod_cast h₁
  have hr₀ : ((S₀.filter (fun e=>head e=v)).card:ℝ) ≤
      ((A\T₁).filter (fun e=>head e=v)).card +
      (B₀.filter (fun e=>head e=v)).card + (F.filter (fun e=>head e=v)).card := by exact_mod_cast h₀
  constructor <;> linarith
end Oberwolfach
