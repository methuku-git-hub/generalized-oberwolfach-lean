module

public import Oberwolfach.MarkedTransformerRowDomains
public import Oberwolfach.MarkedExtensionRows

@[expose] public section

/-! Lower counts for the actual transformer row choices. Up to two rim
requirements and two spoke requirements cost four density factors. The
error remains normalized by the original outer set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

 theorem marked_row_density_product_lower (S:Finset (Bool×Bool×V)) (J:Finset (Bool×U))
    (p p₀ pK:ℝ) (s:Bool→U→ℝ) (hp:0<p) (hp1:p≤1)
    (hp₀:p≤p₀) (hpK:p≤pK) (hs:∀ j u,p≤s j u)
    (hS:S.card≤2) (hJ:J.card≤2):
    p^4≤(∏ a∈S,if a.1 then pK else p₀)*(∏ a∈J,s a.1 a.2):=by
  have h₁:p^S.card≤∏ a∈S,if a.1 then pK else p₀:=by
    calc
      _ = ∏ _a∈S,p:=by simp
      _ ≤ _:=Finset.prod_le_prod₀ (fun _ _=>hp.le) (by intro a ha;cases a.1 <;> simp [hp₀,hpK])
  have h₂:p^J.card≤∏ a∈J,s a.1 a.2:=by
    calc
      _ = ∏ _a∈J,p:=by simp
      _ ≤ _:=Finset.prod_le_prod₀ (fun _ _=>hp.le) (fun a _=>hs a.1 a.2)
  calc
    _ ≤ p^(S.card+J.card):=pow_le_pow_of_le_one hp.le hp1 (by omega)
    _ = p^S.card*p^J.card:=pow_add _ _ _
    _ ≤ _:=mul_le_mul h₁ h₂ (pow_nonneg hp.le _) ((pow_nonneg hp.le _).trans h₁)

 theorem marked_row_count_le_candidates (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop)
    (A C:Finset V) (hCA:C⊆A) (S:Finset (Bool×Bool×V)) (J:Finset (Bool×U)):
    markedRelationRowCount R H C S J≤
      ((A.filter (fun z=>(∀ a∈S,R (markedRowRim a z))∧∀ a∈J,H a.1 z a.2)).card:ℝ):=by
  rw [markedRelationRowCount_card]
  exact_mod_cast Finset.card_le_card (show C.filter (fun z=>(∀ a∈S,R (markedRowRim a z))∧∀ a∈J,H a.1 z a.2)⊆
    A.filter (fun z=>(∀ a∈S,R (markedRowRim a z))∧∀ a∈J,H a.1 z a.2) from
    fun z hz=>Finset.mem_filter.mpr ⟨hCA (Finset.mem_filter.mp hz).1,(Finset.mem_filter.mp hz).2⟩)

 theorem marked_transformer_row_lower (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (R:(V×V)⊕(V×V)→Prop) (H:Bool→V→U→Prop) (A:Finset V)
    (S:Finset (Bool×Bool×V)) (J:Finset (Bool×U))
    (γ p p₀ pK ε loss:ℝ) (s:Bool→U→ℝ)
    (hγ:0<γ) (hp:0<p) (hp1:p≤1) (hp₀:p≤p₀) (hpK:p≤pK) (hs:∀ j u,p≤s j u)
    (hS:S.card≤2) (hJ:J.card≤2)
    (hdomain:γ*A.card-loss≤((markedRowDomain P π b A S ∅).card:ℝ))
    (hloss:loss≤γ*A.card/2) (hε:ε≤p^4*γ/4)
    (hcount:(∏ a∈S,if a.1 then pK else p₀)*(∏ a∈J,s a.1 a.2)*
      (markedRowDomain P π b A S ∅).card-ε*A.card≤
      markedRelationRowCount R H (markedRowDomain P π b A S ∅) S J):
    (p^4*γ/4)*A.card≤
      ((A.filter (fun z=>(∀ a∈S,R (markedRowRim a z))∧∀ a∈J,H a.1 z a.2)).card:ℝ):=by
  have hprod:=marked_row_density_product_lower S J p p₀ pK s hp hp1 hp₀ hpK hs hS hJ
  have hdom:γ*A.card/2≤((markedRowDomain P π b A S ∅).card:ℝ):=by linarith only [hdomain,hloss]
  have hmul:=mul_le_mul hprod hdom (by positivity : 0≤γ*A.card/2) ((pow_nonneg hp.le 4).trans hprod)
  have he:=mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α:=ℝ) A.card)
  have hc:=marked_row_count_le_candidates R H A (markedRowDomain P π b A S ∅)
    (Finset.filter_subset _ _) S J
  nlinarith only [hmul,he,hcount,hc]

end Oberwolfach
