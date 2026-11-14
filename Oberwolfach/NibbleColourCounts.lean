module

public import Oberwolfach.ColourEventWitnesses

@[expose] public section

/-! Counts of colours assigned and rejected in prescribed vertex sets.
The certificate is constructed from actual vertices and their conflicts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def assignedSetIndices {V C J : Type*}
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) : Finset J :=
  Q.filter (fun j=>colourAssignedIn (T j) σ c)

def rejectedSetIndices {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) : Finset J :=
  Q.filter (fun j=>colourRejectedIn G (T j) σ c)

def nibbleColourCount {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (L : Finset C) (a b : ℕ)
    (σ : V → C×Bool) : ℝ :=
  (L.filter (fun c=>a≤(assignedSetIndices Q T σ c).card ∧
    b≤(rejectedSetIndices G Q T σ c).card)).card

theorem rejectedSetIndices_subset_assigned {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) :
    rejectedSetIndices G Q T σ c⊆assignedSetIndices Q T σ c := by
  intro j hj
  obtain ⟨hj,hv⟩ := Finset.mem_filter.mp hj
  obtain ⟨v,hv,hc,_⟩ := hv
  exact Finset.mem_filter.mpr ⟨hj,v,hv,hc⟩

theorem nibbleColourCount_witness
    {V C J : Type*} [DecidableEq V] [Fintype J] (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (σ : V → C×Bool) (c : C) {a b : ℕ}
    (ha : a≤(assignedSetIndices Q T σ c).card)
    (hb : b≤(rejectedSetIndices G Q T σ c).card) :
    ∃ W : Finset V,W.card≤3*Q.card ∧ (∀ v∈W,(σ v).1=c) ∧
      ∀ τ,(∀ v∈W,σ v=τ v) →
        a≤(assignedSetIndices Q T τ c).card ∧
        b≤(rejectedSetIndices G Q T τ c).card := by
  classical
  obtain ⟨A,hA,hcolA,hkeepA⟩ := witnessed_count_threshold
    (fun j τ=>colourAssignedIn (T j) τ c) Q Prod.fst σ c
    (fun j _ hj=>colourAssignedIn_witness (T j) σ c hj) ha
  obtain ⟨B,hB,hcolB,hkeepB⟩ := witnessed_count_threshold
    (fun j τ=>colourRejectedIn G (T j) τ c) Q Prod.fst σ c
    (fun j _ hj=>colourRejectedIn_witness G (T j) σ c hj) hb
  refine ⟨A∪B,?_,?_,?_⟩
  · have hcard := Finset.card_union_le A B
    omega
  · intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact hcolA v hv
    · exact hcolB v hv
  · intro τ he
    exact ⟨hkeepA τ (fun v hv=>he v (Finset.mem_union_left _ hv)),
      hkeepB τ (fun v hv=>he v (Finset.mem_union_right _ hv))⟩

theorem nibbleColourCount_certificate
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (L : Finset C) (a b : ℕ) :
    HasCoordinateCertificateBound (nibbleColourCount G Q T L a b)
      1 ((3*(Q.card : ℝ))*(L.card : ℝ)) := by
  classical
  let P : C → (V → C×Bool) → Prop := fun c σ=>
    c∈L ∧ a≤(assignedSetIndices Q T σ c).card ∧
      b≤(rejectedSetIndices G Q T σ c).card
  have hex (σ : V → C×Bool) (c : C) (h : P c σ) :
      ∃ W : Finset V,W.card≤3*Q.card ∧ (∀ v∈W,(σ v).1=c) ∧
        ∀ τ,(∀ v∈W,σ v=τ v) → P c τ := by
    obtain ⟨W,hsize,hcol,hkeep⟩ := nibbleColourCount_witness G Q T σ c h.2.1 h.2.2
    exact ⟨W,hsize,hcol,fun τ he=>⟨h.1,hkeep τ he⟩⟩
  let W : (V → C×Bool) → C → Finset V := fun σ c=>
    if h : P c σ then Classical.choose (hex σ c h) else ∅
  have hW (σ : V → C×Bool) (c : C) (h : P c σ) :
      (W σ c).card≤3*Q.card ∧ (∀ v∈W σ c,(σ v).1=c) ∧
        ∀ τ,(∀ v∈W σ c,σ v=τ v) → P c τ := by
    dsimp only [W]
    rw [dif_pos h]
    exact Classical.choose_spec (hex σ c h)
  have hc := monochromatic_witness_certificate P W Prod.fst L
    (fun _ _ h=>h.1) (fun σ c h=>(hW σ c h).1)
    (fun σ c h=>(hW σ c h).2.1) (fun σ c h=>(hW σ c h).2.2)
  convert hc using 1
  ·
    funext σ
    unfold nibbleColourCount
    apply congrArg (fun n : ℕ=>(n : ℝ))
    apply congrArg Finset.card
    ext c
    simp [P]
  · push_cast
    ring

end Oberwolfach
