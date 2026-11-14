module

public import Oberwolfach.MarkedCorrectionForbiddenBound

@[expose] public section
/-! Extract the physical rim pairs from a reserved set without counting
spokes as rim resources. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Nonempty V]

def markedReservedRimPairs (C:Finset (Finset V⊕(V×U))):Finset (Finset V):=
  (C.filter (fun z=>∃ e:Finset V,z=Sum.inl e)).image (Sum.elim id (fun _=>∅))

omit [Nonempty V] in
theorem marked_reserved_rim_pairs_membership (C:Finset (Finset V⊕(V×U))) (e:Finset V):
    e∈markedReservedRimPairs C ↔ Sum.inl e∈C :=by
  constructor
  · intro he
    obtain ⟨z,hz,heq⟩:=Finset.mem_image.mp he
    obtain ⟨hzC,⟨e',rfl⟩⟩:=Finset.mem_filter.mp hz
    simpa using heq ▸ hzC
  · intro he
    exact Finset.mem_image.mpr ⟨Sum.inl e,Finset.mem_filter.mpr ⟨he,⟨e,rfl⟩⟩,rfl⟩

omit [Nonempty V] in
theorem marked_reserved_rim_pairs_card (C:Finset (Finset V⊕(V×U))):
    (markedReservedRimPairs C).card≤C.card :=by
  exact Finset.card_image_le.trans (Finset.card_filter_le _ _)

theorem marked_reserved_correction_forbidden_bound
    (P:V×V→Prop) (C:Finset (Finset V⊕(V×U))) (v:V):
    ((Finset.univ.filter (fun e:{a:V×V // P a}=>e.val.2=v ∧
      Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)).card:ℝ)≤C.card :=by
  have heq:Finset.univ.filter (fun e:{a:V×V // P a}=>e.val.2=v ∧
      Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)=
    Finset.univ.filter (fun e:{a:V×V // P a}=>e.val.2=v ∧
      ({e.val.1,e.val.2}:Finset V)∈markedReservedRimPairs C):=by
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,marked_reserved_rim_pairs_membership]
  rw [heq]
  exact (marked_correction_forbidden_incoming_bound P (markedReservedRimPairs C) v).trans
    (Nat.cast_le.mpr (marked_reserved_rim_pairs_card C))

variable (P:V×V→Prop)
local instance reservedCandidateArcDecEq : DecidableEq {e:V×V // P e} := fun a b => Classical.propDecidable (a=b)

/-- Protect the rim pairs in the actual mixed reserved resource set. -/
theorem marked_correction_protects_reserved_resources
    (S₀ S₁ T₀ T₁ B₀ B₁:Finset {e:V×V // P e})
    (C:Finset (Finset V⊕(V×U))) (b:ℕ) (rho eta:ℝ) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hdis:Disjoint T₀ T₁) (h₀:S₀\T₀⊆B₀) (h₁:S₁\T₁⊆B₁)
    (hdev:∀ v, |(directedInCount P T₁ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (base₀ base₁ loss₀ loss₁:V→ℝ)
    (hbase₀:∀ v, base₀ v≤(S₀.filter (fun e=>e.val.2=v)).card)
    (hbase₁:∀ v, base₁ v≤(S₁.filter (fun e=>e.val.2=v)).card)
    (hloss₀:∀ v, ((B₀.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₀ v)
    (hloss₁:∀ v, ((B₁.filter (fun e=>e.val.2=v)).card:ℝ)≤loss₁ v)
    (hmargin₀:∀ v, rho*Fintype.card V≤base₀ v-loss₀ v-C.card)
    (hmargin₁:∀ v, rho*Fintype.card V≤base₁ v-loss₁ v-C.card):
    let F:=Finset.univ.filter (fun e:{a:V×V // P a}=>Sum.inl ({e.val.1,e.val.2}:Finset V)∈C)
    let A:=(T₀∪T₁)\F
    ∃ M:Finset {e:V×V // P e},
      (∀ v, directedInCount P M v=b) ∧ symmDiff M T₁⊆A ∧
      (∀ e, Sum.inl ({e.val.1,e.val.2}:Finset V)∈C → (e∈M ↔ e∈T₁)) ∧
      (∀ v, ((physicalEdgeGraph (changedDirectedPhysicalEdges P M T₁)).degree v:ℝ) ≤
        (1+2/rho)*eta*Fintype.card V+(Fintype.card V:ℝ)^(3/5:ℝ)) :=by
  intro F A
  have hcard:((markedReservedRimPairs C).card:ℝ)≤C.card:=Nat.cast_le.mpr (marked_reserved_rim_pairs_card C)
  have h0:∀ v,rho*Fintype.card V≤base₀ v-loss₀ v-(markedReservedRimPairs C).card:=by
    intro v
    linarith [hmargin₀ v]
  have h1:∀ v,rho*Fintype.card V≤base₁ v-loss₁ v-(markedReservedRimPairs C).card:=by
    intro v
    linarith [hmargin₁ v]
  have hF: F=Finset.univ.filter (fun e:{a:V×V // P a}=>
      ({e.val.1,e.val.2}:Finset V)∈markedReservedRimPairs C):=by
    ext e
    simp [F,marked_reserved_rim_pairs_membership]
  have hh:=marked_correction_with_reserved_pair_count P S₀ S₁ T₀ T₁ B₀ B₁ (markedReservedRimPairs C)
    b rho eta hrho heta hetaR hdis h₀ h₁ hdev base₀ base₁ loss₀ loss₁ hbase₀ hbase₁ hloss₀ hloss₁ h0 h1
  rw [←hF] at hh
  obtain ⟨M,hM,hA,hC,hB⟩:=hh
  refine ⟨M,hM,hA,?_,hB⟩
  intro e he
  exact hC e ((marked_reserved_rim_pairs_membership C _).mpr he)
end Oberwolfach
