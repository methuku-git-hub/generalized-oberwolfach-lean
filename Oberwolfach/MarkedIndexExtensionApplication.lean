module

public import Oberwolfach.MarkedExtensionRows

@[expose] public section

/-! Every separated index request is read from the same marked index
estimate. The supplied hub-dependent marginals are bounded, not replaced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def markedExtensionIndexRequests (X Y : Finset V) : Finset (Bool×V) :=
  X.image (fun v=>(false,v)) ∪ Y.image (fun v=>(true,v))

theorem markedExtensionIndexRequests_mem (X Y : Finset V) (a : Bool×V) :
    a∈markedExtensionIndexRequests X Y ↔ (a.1=false ∧ a.2∈X) ∨ (a.1=true ∧ a.2∈Y) := by
  obtain ⟨b,v⟩:=a
  cases b <;> simp [markedExtensionIndexRequests]

theorem markedExtensionIndexRequests_card (X Y : Finset V) :
    (markedExtensionIndexRequests X Y).card=X.card+Y.card := by
  have hdis : Disjoint (X.image (fun v=>(false,v))) (Y.image (fun v=>(true,v))) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨v,hv,he⟩:=Finset.mem_image.mp ha
    obtain ⟨w,hw,hf⟩:=Finset.mem_image.mp hb
    have hh:=congrArg Prod.fst (he.trans hf.symm)
    cases hh
  rw [markedExtensionIndexRequests,Finset.card_union_of_disjoint hdis]
  rw [Finset.card_image_of_injective _ (by intro v w h;exact Prod.mk.inj h |>.2),
    Finset.card_image_of_injective _ (by intro v w h;exact Prod.mk.inj h |>.2)]

theorem markedExtensionIndexRequests_separated (π : Equiv.Perm V) (b : ℕ) (X Y : Finset V)
    (hXY : Disjoint X Y) (hsep : ((X∪Y):Set V).Pairwise (fun v w=>¬PermutationClose π b v w)) :
    ∀ a∈markedExtensionIndexRequests X Y,∀ e∈markedExtensionIndexRequests X Y,
      a≠e → ¬PermutationClose π b a.2 e.2 := by
  intro a ha e he hne
  have ha':=(markedExtensionIndexRequests_mem X Y a).mp ha
  have he':=(markedExtensionIndexRequests_mem X Y e).mp he
  have ham : a.2∈X∪Y := by rcases ha' with h|h;exact Finset.mem_union_left _ h.2;exact Finset.mem_union_right _ h.2
  have hem : e.2∈X∪Y := by rcases he' with h|h;exact Finset.mem_union_left _ h.2;exact Finset.mem_union_right _ h.2
  have hroot : a.2≠e.2 := by
    intro h
    rcases ha' with ha'|ha' <;> rcases he' with he'|he'
    · exact hne (Prod.ext (ha'.1.trans he'.1.symm) h)
    · exact Finset.disjoint_left.mp hXY ha'.2 (h.symm ▸ he'.2)
    · exact Finset.disjoint_left.mp hXY (h.symm ▸ he'.2) ha'.2
    · exact hne (Prod.ext (ha'.1.trans he'.1.symm) h)
  exact hsep (by simpa using ham) (by simpa using hem) hroot

theorem markedExtensionIndexRequests_count (H : Bool→V→U→Prop) (B : Finset U) (X Y : Finset V) :
    markedIndexCountWithSpokes H B (markedExtensionIndexRequests X Y)=
      ((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ) := by
  have he : common (common B X (fun v=>Finset.univ.filter (H false v))) Y
      (fun v=>Finset.univ.filter (H true v))=
      B.filter (fun u=>∀ a∈markedExtensionIndexRequests X Y,H a.1 a.2 u) := by
    ext u
    simp [common,markedExtensionIndexRequests,and_assoc]
  rw [he]
  simp only [markedIndexCountWithSpokes,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem marked_index_event_extension_lower (π : Equiv.Perm V) (d h : ℕ) (B : Finset U)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (g : Γ) (j : Color) (pstar ε : ℝ)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1)
    (hq : ∀ u∈B,pstar≤q u g) (hs : ∀ u∈B,pstar≤s u j) (hε : ε≤pstar^h/2)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hindices : MarkedIndicesWithSpokes π d h B q s g j (ε*B.card) σ H)
    (X Y : Finset V) (hXY : Disjoint X Y) (hsize : (X∪Y).card≤h)
    (hsep : ((X∪Y):Set V).Pairwise (fun v w=>¬PermutationClose π (3*d) v w)) :
    (pstar^h/2)*B.card≤((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ) := by
  let J:=markedExtensionIndexRequests X Y
  have hJ : J.card≤h := by
    rw [markedExtensionIndexRequests_card]
    rwa [Finset.card_union_of_disjoint hXY] at hsize
  have hprod (u : U) (hu:u∈B) : pstar^h≤∏ a∈J,if a.1 then q u g else s u j := by
    calc
      _ ≤ pstar^J.card := pow_le_pow_of_le_one hpstar.le hpstar1 hJ
      _ = ∏ _a∈J,pstar := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _=>hpstar.le) (by
        intro a ha
        split_ifs
        · exact hq u hu
        · exact hs u hu)
  have hmean : pstar^h*B.card≤∑ u∈B,∏ a∈J,if a.1 then q u g else s u j := by
    have hh:=Finset.sum_le_sum hprod
    simpa [mul_comm] using hh
  have hh:=hindices J hJ (markedExtensionIndexRequests_separated π (3*d) X Y hXY hsep)
  have hlo:=(abs_lt.mp hh).1
  rw [markedExtensionIndexRequests_count] at hlo
  have he:=mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg B.card)
  nlinarith only [hlo,hmean,he]

end Oberwolfach
