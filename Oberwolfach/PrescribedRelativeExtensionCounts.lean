module

public import Oberwolfach.PrescribedExtensionCounts
public import Oberwolfach.LocalExtensionCounts

@[expose] public section

/-! The extension inequalities used by the prescribed-edge packing follow
from the original relative counts, including external roots and fixed hub
domains. Later exclusion of vertices is charged without a density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem prescribed_relative_extension_counts (P Q F:SimpleGraph V) (H:V→U→Prop)
    (A X:Finset V) (U₀ B:Finset U) (p₀ q p γ ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (hq:p₀≤q) (hp:p₀≤p) (hγ:0<γ) (hγ1:γ≤1)
    (hε:ε≤p₀^6*γ/4)
    (hdeg:∀ v,(1/2+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hXA:((A\X).card:ℝ)≤p₀^6*γ*A.card/8)
    (hBU:((U₀\B).card:ℝ)≤p₀^6*γ*U₀.card/8)
    (hrow:∀ S:Finset V,∀ J:Finset U,J⊆U₀ → S.card≤2 → J.card≤1 →
      |((common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤2 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common U₀ S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*U₀.card|≤ε*U₀.card):
    (∀ u∈U₀,∀ a c,(p₀^6*γ/8)*A.card≤
      (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) ∧
    (∀ a c,¬F.Adj a c → (p₀^6*γ/8)*U₀.card≤((B.filter (fun u=>H a u∧H c u)).card:ℝ)):=by
  let β:=p₀^6*γ/4
  have hpow:p₀^6≤p₀^2:=pow_le_pow_of_le_one hp₀.le hp₀1 (by omega)
  have hβsmall:2*β≤p₀^2:=by
    have hh:=mul_le_mul_of_nonneg_left hγ1 (pow_nonneg hp₀.le 6)
    dsimp [β];nlinarith only [hh,hpow,pow_nonneg hp₀.le 2]
  constructor
  · intro u hu a c
    let S:Finset V:={a,c}
    let J:Finset U:={u}
    have hrel:=hrow S J (by
      intro z hz
      have he:z=u:=by simpa only [J,Finset.mem_singleton] using hz
      exact he ▸ hu)
      Finset.card_le_two (by simp [J])
    have hh:=extension_relative_row_lower P Q ⊥ A S J
      (fun u=>Finset.univ.filter (fun v=>H v u)) 2 γ p₀ q p ε 0
      (by omega) (by omega) hγ hγ1 hp₀ hp₀1 hq hp (by norm_num)
      Finset.card_le_two (by simp [J]) (by simp only [mul_zero];positivity) hε
      (by intro v hv;norm_num;exact hdeg v) (by intro v hv;simp)
      (by
        have ht:q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card-ε*A.card≤
          ((common (common A S (fun v=>Q.neighborFinset v)) J (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ):=by
            linarith only [(abs_le.mp hrel).1]
        convert ht using 1 <;> congr! <;> ext v w <;> simp)
    have he (Z:Finset V):common (common Z S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))=Z.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v):=by
      ext v;simp [mem_common_iff,S,J];tauto
    rw [he] at hh
    have hcard:((A.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)).card:ℝ)≤
      (X.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)).card+(A\X).card:=by
      exact_mod_cast common_domain_restriction_card A X (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)
    have he':X.filter (fun v=>H v u∧Q.Adj a v∧Q.Adj c v)=
        (X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c:=by
      ext v;simp;tauto
    rw [he'] at hcard
    linarith only [hh,hcard,hXA]
  · intro a c hfac
    have hsep:∀ v∈({a,c}:Finset V),∀ w∈({a,c}:Finset V),¬F.Adj v w:=by
      intro v hv w hw h
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
      rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
      · exact F.loopless.irrefl _ h
      · exact hfac h
      · exact hfac h.symm
      · exact F.loopless.irrefl _ h
    have hrel:=hindex {a,c} Finset.card_le_two hsep
    have hcoef:2*β≤p^({a,c}:Finset V).card:=hβsmall.trans
      ((pow_le_pow_of_le_one hp₀.le hp₀1 Finset.card_le_two).trans
        (pow_le_pow_left₀ hp₀.le hp _))
    have hm:=mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg U₀.card)
    have herr:=mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg U₀.card)
    have he:common U₀ ({a,c}:Finset V) (fun v=>Finset.univ.filter (H v))=
        U₀.filter (fun u=>H a u∧H c u):=by ext u;simp [mem_common_iff]
    rw [he] at hrel
    have hcard:((U₀.filter (fun u=>H a u∧H c u)).card:ℝ)≤
      (B.filter (fun u=>H a u∧H c u)).card+(U₀\B).card:=by
      exact_mod_cast common_domain_restriction_card U₀ B (fun u=>H a u∧H c u)
    dsimp [β] at hm
    linarith only [(abs_le.mp hrel).1,hm,herr,hcard,hBU]

end Oberwolfach
