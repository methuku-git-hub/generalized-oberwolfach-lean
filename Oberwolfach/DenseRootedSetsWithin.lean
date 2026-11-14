module

public import Oberwolfach.RootedAdmissibleMany
public import Oberwolfach.InducedSetEmbedding

@[expose] public section

/-! Count dense conflict-free rooted sets inside a specified vertex domain.
The ambient graph is retained in the conclusion, so external-root callers
can first enlarge their neighbourhood and then apply this result. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem dense_rooted_sets_within (s : ℕ) (α : ℝ) (hα : 0<α) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → ∀ L : ℝ,0≤L → ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V],
    ∀ (P F : SimpleGraph V) (B T : Finset V),N≤B.card → T.card=s → T⊆B → ∀ δ : ℝ,
    (∀ v∈B,(δ+α)*(B.card:ℝ)≤((P.neighborFinset v∩B).card:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) → (∀ x∈T,∀ y∈T,¬F.Adj x y) →
    (B.card:ℝ)^k/((2:ℝ)^(k+1)*k.factorial)≤
      Fintype.card {S : FixedSubset V (s+k) // T⊆S.val ∧ S.val⊆B ∧
        (∀ v∈S.val,(δ+α/2)*(s+k:ℝ)<((P.neighborFinset v∩S.val).card:ℝ)) ∧
        (∀ x∈S.val,∀ y∈S.val,¬F.Adj x y)} := by
  obtain ⟨K,hK⟩ := rootedSubset_dense_conflict_free_many s α hα
  refine ⟨K,?_⟩
  intro k hk L hL
  obtain ⟨N,hN⟩ := hK k hk L hL
  refine ⟨N,?_⟩
  intro V _ _ P F B T hNB hT hTB δ hP hF hind
  let Z := T.subtype (fun v=>v∈B)
  have hZ : Z.card=s := by
    dsimp [Z]
    rw [Finset.card_subtype]
    have he : T.filter (fun v=>v∈B)=T := Finset.filter_eq_self.mpr hTB
    rw [he,hT]
  clear hT
  subst s
  have hcardB : Fintype.card {v : V // v∈B}=B.card := Fintype.card_coe B
  have hp (v : {v : V // v∈B}) :
      (δ+α)*Fintype.card {v : V // v∈B}≤((P.induce (B:Set V)).degree v:ℝ) := by
    rw [hcardB,induced_degree_intersection]
    exact hP v.val v.property
  have hf (v : {v : V // v∈B}) : ((F.induce (B:Set V)).degree v:ℝ)≤L := by
    have hh : ((F.induce (B:Set V)).degree v:ℝ)≤F.degree v.val := by
      exact_mod_cast induced_degree_le_ambient F B v
    exact hh.trans (hF v.val)
  have hz : ∀ x∈Z,∀ y∈Z,¬(F.induce (B:Set V)).Adj x y := by
    intro x hx y hy hxy
    exact hind x.val (Finset.mem_subtype.mp hx) y.val (Finset.mem_subtype.mp hy) hxy
  have hh := hN {v : V // v∈B} (by simpa only [hcardB] using hNB)
    (P.induce (B:Set V)) (F.induce (B:Set V)) Z rfl δ hp hf hz
  let A := {S : RootedSubset {v : V // v∈B} Z k //
    (∀ v∈S.val.val,(δ+α/2)*(Z.card+k:ℝ)<(((P.induce (B:Set V)).neighborFinset v∩S.val.val).card:ℝ)) ∧
    (∀ x∈S.val.val,∀ y∈S.val.val,¬(F.induce (B:Set V)).Adj x y)}
  let D := {S : FixedSubset V (Z.card+k) // T⊆S.val ∧ S.val⊆B ∧
    (∀ v∈S.val,(δ+α/2)*(Z.card+k:ℝ)<((P.neighborFinset v∩S.val).card:ℝ)) ∧
    (∀ x∈S.val,∀ y∈S.val,¬F.Adj x y)}
  let f (S : A) : D := ⟨inducedSetEmbedding B S.val.val,by
    refine ⟨?_,inducedSetEmbedding_subset B S.val.val,?_,
      inducedSetEmbedding_conflict_free F B S.val.val S.property.2⟩
    · intro v hv
      have hvB := hTB hv
      have hvZ : (⟨v,hvB⟩:{v : V // v∈B})∈Z := Finset.mem_subtype.mpr hv
      exact Finset.mem_map.mpr ⟨⟨v,hvB⟩,S.val.property hvZ,rfl⟩
    · intro v hv
      obtain ⟨v',hv',rfl⟩ := Finset.mem_map.mp hv
      have hh := S.property.1 v' hv'
      rw [inducedSetEmbedding_degree] at hh
      exact hh⟩
  have hinj : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    apply Subtype.ext
    exact inducedSetEmbedding_injective B (Z.card+k) (congrArg Subtype.val he)
  have hc : Fintype.card A≤Fintype.card D := Fintype.card_le_of_injective f hinj
  have hh' : (B.card:ℝ)^k/((2:ℝ)^(k+1)*k.factorial)≤Fintype.card A := by
    simpa only [A,hcardB] using hh
  have hout := hh'.trans (show (Fintype.card A:ℝ)≤Fintype.card D by exact_mod_cast hc)
  simpa only [D,Nat.cast_add] using hout

end Oberwolfach
