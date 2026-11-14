module

public import Oberwolfach.OrdinaryEndpointRelativeCounts

@[expose] public section

/-! Conversion of ordinary endpoint counts to their actual part sizes.
The original errors retain |A| and |B|; no random subdomain replaces either. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem endpoint_spoke_normalisation (m b c p p₀ ε e:ℝ)
    (hb:0≤b) (hp₀:0<p₀) (hp:p₀≤p) (hp1:p≤1) (hε:0≤ε)
    (he:0≤e) (hεsmall:ε≤p₀/2) (hεe:4*ε≤e*p₀)
    (hm:|m-p*b|≤ε*b) :
    p₀*b/2≤m ∧
    (|c-p^2*b|≤ε*b → (p-e)*m≤c) ∧
    (c≤p^3*b+ε*b → c≤(p^2+e)*m) := by
  have hp0:0≤p:=hp₀.le.trans hp
  have hp2:0≤p^2:=sq_nonneg p
  have hp21:p^2≤1:=by nlinarith only [hp0,hp1]
  have hmlo:= (abs_le.mp hm).1
  have hmhi:= (abs_le.mp hm).2
  have hpB:=mul_le_mul_of_nonneg_right hp hb
  have heB:=mul_le_mul_of_nonneg_right hεsmall hb
  have hm':p₀*b/2≤m:=by linarith only [hmlo,hpB,heB]
  have heM:=mul_le_mul_of_nonneg_left hm' he
  have hee:=mul_le_mul_of_nonneg_right hεe hb
  have hbudget:2*ε*b≤e*m:=by nlinarith only [heM,hee]
  refine ⟨hm',?_,?_⟩
  · intro hc
    have hmul:=mul_le_mul_of_nonneg_left hmhi hp0
    have hεp:=mul_le_mul_of_nonneg_right hp1 (mul_nonneg hε hb)
    nlinarith only [hmul,hεp,hbudget,(abs_le.mp hc).1]
  · intro hc
    have hmul:=mul_le_mul_of_nonneg_left hmlo hp2
    have hεp:=mul_le_mul_of_nonneg_right hp21 (mul_nonneg hε hb)
    nlinarith only [hmul,hεp,hbudget,hc]

theorem endpoint_column_normalisation (m b c a q p ε:ℝ)
    (hp:0≤p) (hp1:p≤1) (hεa:0≤ε*a)
    (hsize:|2*m-q*b|≤ε*a) (hcount:|c-q*p*b|≤ε*a)
    (hbudget:2*ε*a≤p*m) : p*m≤c := by
  have hh:=mul_le_mul_of_nonneg_left (abs_le.mp hsize).2 hp
  have he:=mul_le_mul_of_nonneg_right hp1 hεa
  nlinarith only [hh,he,hbudget,(abs_le.mp hcount).1]

variable {V U:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_counts_normalised (P R F:SimpleGraph V) (H:V→U→Prop)
    (A:Finset V) (B:Finset U) (x:V) (q p p₀ ε e:ℝ)
    (hRP:R≤P) (hFx:∀ v,R.Adj x v → ¬F.Adj x v)
    (hp₀:0<p₀) (hp:p₀≤p) (hp1:p≤1) (hε:0≤ε) (he:0≤e)
    (hεsmall:ε≤p₀/2) (hεe:4*ε≤e*p₀)
    (hbal:(A∩R.neighborFinset x).card=2*(B.filter (H x)).card)
    (hbudget:2*ε*A.card≤p*(B.filter (H x)).card)
    (hrow:∀ S:Finset V,∀ J:Finset U,S.card≤1 → J.card≤1 →
      |((common (common A S (fun v=>R.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*B.card|≤ε*B.card) :
    let S:=A∩R.neighborFinset x
    let T:=B.filter (H x)
    p₀*B.card/2≤(T.card:ℝ) ∧
    (∀ v∈S,(p-e)*T.card≤((T.filter (H v)).card:ℝ)) ∧
    (∀ u∈B,p*T.card≤((S.filter (fun v=>H v u)).card:ℝ)) ∧
    (∀ v∈S,∀ w∈S,v≠w → ¬F.Adj v w →
      ((T.filter (fun u=>H v u∧H w u)).card:ℝ)≤(p^2+e)*T.card) := by
  dsimp only
  obtain ⟨hS,hT,hrows,hcols,hcodeg⟩:=ordinary_endpoint_counts_from_common P R F H A B x q p ε hRP hFx hrow hindex
  have hnorm (c:ℝ):=endpoint_spoke_normalisation (B.filter (H x)).card B.card c p p₀ ε e
    (Nat.cast_nonneg _) hp₀ hp hp1 hε he hεsmall hεe hT
  refine ⟨(hnorm 0).1,?_,?_,?_⟩
  · intro v hv
    exact (hnorm _).2.1 (hrows v hv)
  · intro u hu
    have hS':|2*(B.filter (H x)).card-q*(A∩P.neighborFinset x).card|≤ε*A.card:=by
      simpa only [hbal,Nat.cast_mul,Nat.cast_ofNat] using hS
    exact endpoint_column_normalisation _ _ _ _ q p ε (hp₀.le.trans hp) hp1 (by positivity)
      hS' (hcols u hu) hbudget
  · intro v hv w hw hvw hfw
    exact (hnorm _).2.2 (hcodeg v hv w hw hvw hfw)

end Oberwolfach
