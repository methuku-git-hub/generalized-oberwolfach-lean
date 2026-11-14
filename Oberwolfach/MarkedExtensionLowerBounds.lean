module

public import Oberwolfach.MarkedExtensionRows

@[expose] public section

/-! The lower-count substitutions for the four marked extension patterns.
Original parent domains and absolute errors are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_extension_target_lower (a domain target count γ p ε loss : ℝ)
    (ha : 0≤a) (hγ : 0<γ) (hp : 0<p) (hdomain : γ*a-loss≤domain)
    (hloss : loss≤γ*a/2) (htarget : p^3≤target)
    (hε : ε≤p^3*γ/4) (hcount : target*domain-ε*a≤count) :
    (p^3*γ/4)*a≤count := by
  have hdom : γ*a/2≤domain := by linarith only [hdomain,hloss]
  have ht0 : 0≤target := (pow_nonneg hp.le _).trans htarget
  have hh:=mul_le_mul htarget hdom (by positivity : 0≤γ*a/2) ht0
  have he:=mul_le_mul_of_nonneg_right hε ha
  nlinarith only [hh,he,hcount]

theorem marked_one_extension_lower (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop) (A : Finset V)
    (hA : A.image π=A) (j : Bool) (v : V) (u : U) (γ p pj sj ε : ℝ)
    (hγ : 0<γ) (hγ1 : γ≤1) (hp : 0<p) (hp1 : p≤1) (hpj : p≤pj) (hsj : p≤sj)
    (hloss : 2*(2*(b:ℝ)+1)≤γ*A.card/2) (hε : ε≤p^3*γ/4)
    (hdeg : ∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ))
    (hcount : pj*sj*(markedRowDomain P π b A (markedOneExtensionRequests j v) ∅).card-ε*A.card≤
      markedRelationRowCount R H (markedRowDomain P π b A (markedOneExtensionRequests j v) ∅)
        (markedOneExtensionRequests j v) {(j,u)}) :
    (p^3*γ/4)*A.card≤((markedOneExtensionSet R H A j v u).card:ℝ) := by
  have ht : p^3≤pj*sj := by
    calc
      _ ≤ p^2 := pow_le_pow_of_le_one hp.le hp1 (by decide)
      _ = p*p := by ring
      _ ≤ _ := mul_le_mul hpj hsj hp.le (hp.le.trans hpj)
  have hd:=marked_one_extension_domain_lower P π b A hA j v γ hγ1 hdeg
  have hh:=marked_extension_target_lower A.card _ _ _ γ p ε (2*(b:ℝ)+1)
    (Nat.cast_nonneg _) hγ hp hd (by linarith only [hloss,Nat.cast_nonneg (α:=ℝ) b]) ht hε hcount
  exact hh.trans (markedRelationRowCount_one_le R H A _ (Finset.filter_subset _ _) j v u)

theorem marked_two_extension_lower (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (R : (V×V)⊕(V×V)→Prop) (H : Bool→V→U→Prop) (A : Finset V)
    (j : Bool) (v w : V) (u : U) (hne : v≠if j then π w else w) (γ p p₀ pj s₀ ε : ℝ)
    (hγ : 0<γ) (hγ1 : γ≤1) (hp : 0<p) (hp₀ : p≤p₀) (hpj : p≤pj) (hs₀ : p≤s₀)
    (hloss : 2*(2*(b:ℝ)+1)≤γ*A.card/2) (hε : ε≤p^3*γ/4)
    (hdeg : ∀ x,(1/2+γ/2)*A.card≤((A∩P.neighborFinset x).card:ℝ))
    (hcount : p₀*pj*s₀*(markedRowDomain P π b A (markedTwoExtensionRequests j v w) ∅).card-ε*A.card≤
      markedRelationRowCount R H (markedRowDomain P π b A (markedTwoExtensionRequests j v w) ∅)
        (markedTwoExtensionRequests j v w) {(false,u)}) :
    (p^3*γ/4)*A.card≤((markedTwoExtensionSet R H A j v w u).card:ℝ) := by
  have ht : p^3≤p₀*pj*s₀ := by
    have hh:=mul_le_mul (mul_le_mul hp₀ hpj hp.le (hp.le.trans hp₀)) hs₀ hp.le
      (mul_nonneg (hp.le.trans hp₀) (hp.le.trans hpj))
    convert hh using 1 <;> ring
  have hd:=marked_two_extension_domain_lower P π b A j v w hne γ hγ1 hdeg
  have hh:=marked_extension_target_lower A.card _ _ _ γ p ε (2*(2*(b:ℝ)+1))
    (Nat.cast_nonneg _) hγ hp hd hloss ht hε hcount
  exact hh.trans (markedRelationRowCount_two_le R H A _ (Finset.filter_subset _ _) j v w u)

theorem marked_extension_index_lower (H : Bool→V→U→Prop) (B : Finset U) (X Y : Finset V)
    (c : ℕ) (p s t ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hs : p≤s) (ht : p≤t)
    (hXY : X.card+Y.card≤c+6) (hε : ε≤p^(c+6)/2)
    (hcount : (s^X.card*t^Y.card-ε)*B.card≤
      ((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ)) :
    (p^(c+6)/2)*B.card≤((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ) := by
  have hprod : p^(c+6)≤s^X.card*t^Y.card := by
    calc
      _ ≤ p^(X.card+Y.card) := pow_le_pow_of_le_one hp.le hp1 hXY
      _ = p^X.card*p^Y.card := pow_add _ _ _
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hp.le hs _) (pow_le_pow_left₀ hp.le ht _)
        (pow_nonneg hp.le _) (pow_nonneg (hp.le.trans hs) _)
  exact (mul_le_mul_of_nonneg_right (by linarith only [hprod,hε]) (Nat.cast_nonneg B.card)).trans hcount

end Oberwolfach
