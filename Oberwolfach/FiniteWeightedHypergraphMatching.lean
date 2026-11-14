module

public import Oberwolfach.DisjointPartWeightedMatching
public import Oberwolfach.MonochromaticHyperedgeCopies
public import Oberwolfach.HypergraphColorPartition

@[expose] public section

/-! The complete three-stage weighted matching construction: vertex
partition, edge partition and independent selection of proper colour classes.
All three common-event bounds are explicit; the final error includes the
first partition's error on the original, fixed weight functions. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_weighted_hypergraph_matching
    (k : ℕ) (hk : 2≤k) (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1/2)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D₀ : ℕ, ∀ D B : ℕ, D₀≤D → (B : ℝ)≤(D : ℝ)^(1-δ) →
      ∀ (V E I C A : Type) [Fintype V] [Fintype E] [Fintype I] [Fintype C] [Fintype A]
        [DecidableEq V] [Nonempty I] [Nonempty C],
      ∀ (R : E → Finset V) (w : A → E → ℝ) (b W L s T t : A → ℝ) (d β u s₀ s₁ s₂ : ℝ),
      (∀ e,(R e).card=k) →
      (∀ v,0<Fintype.card (HypergraphEdgesAt R v)) →
      (∀ v,(Fintype.card (HypergraphEdgesAt R v) : ℝ)≤d) →
      (∀ v z,v≠z → ((Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card : ℝ)≤β) →
      0≤d → 0≤β → 0≤u →
      (∀ a,0<b a) → (∀ a e,0≤w a e ∧ w a e≤b a) →
      (∀ a,∑ e,w a e=W a) → (∀ a,0<W a) →
      (∀ a v,hypergraphWeightedDegree R (w a) v≤L a) →
      (∀ a,0≤s a) → (∀ a,0≤t a) → 0≤s₀ → 0≤s₁ → 0≤s₂ →
      (∑ v : V,∑ _i : I,2*Real.exp (-2*u^2/(β*((k : ℝ)-1)*Fintype.card (HypergraphEdgesAt R v))))+
        (∑ a : A,∑ _i : I,2*Real.exp (-2*(s a)^2/(L a*k*W a)))<1 →
      (∑ _i : I,∑ _v : V,∑ _c : C,
        Real.exp ((d/(Fintype.card I : ℝ)^(k-1)+u)/Fintype.card C*(Real.exp s₀-1)-s₀*((D : ℝ)+1)))+
      ((∑ _i : I,∑ _v : V,∑ _z : V,∑ _c : C,
        Real.exp (β/Fintype.card C*(Real.exp s₁-1)-s₁*((B : ℝ)+1)))+
      (∑ _i : I,∑ a : A,∑ _c : C,
        Real.exp (((W a/(Fintype.card I : ℝ)^k+s a)/Fintype.card C*(Real.exp s₂-1)-s₂*T a)/b a)))<1 →
      (∑ a : A,2*Real.exp (-2*(t a)^2/(∑ _i : I,(T a)^2)))<1 →
      ∃ M : Finset E,
        (∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
        ∀ a,|(∑ e∈M,w a e)-W a/
          ((Fintype.card I : ℝ)^(k-1)*(Fintype.card C : ℝ)*⌈(1+ε)*(D : ℝ)⌉₊)|
          <t a+(Fintype.card I : ℝ)*s a/((Fintype.card C : ℝ)*⌈(1+ε)*(D : ℝ)⌉₊) := by
  classical
  obtain ⟨N,hN⟩ := weighted_matching_on_disjoint_parts k (by omega) ε δ hε hε1 hδ hδ1
  refine ⟨max 1 N,?_⟩
  intro D B hD hB V E I C A _ _ _ _ _ _ _ _ R w b W L s T t d β u s₀ s₁ s₂
    hsize hpositive hdegree hcodeg hd hβ hu hb hw htotal hW hL hs ht hs₀ hs₁ hs₂ hvertex hedge hselect
  obtain ⟨σ,hσdeg,hσweight⟩ := hypergraphColorPartition_exists (C:=I) R k hk hsize hpositive β hβ
    (fun v z hz=>hcodeg v z hz.symm) w (fun a e=>(hw a e).1)
    (fun a=>by rw [htotal];exact hW a) L hL (fun _=>u) s (fun _=>hu) hs
    (by simpa only [htotal] using hvertex)
  let E' := MonochromaticHyperedge R σ
  letI : Fintype E' := Fintype.ofFinite E'
  let R' : E' → Finset V := fun e=>R e.2.val
  let w' : A → E' → ℝ := fun a e=>w a e.2.val
  have hparts : ∀ e f : E',e.1≠f.1 → Disjoint (R' e) (R' f) :=
    monochromatic_copies_disjoint R σ
  have hdeg' : ∀ i v,((Finset.univ.filter (fun e : E'=>e.1=i ∧ v∈R' e)).card : ℝ)≤
      d/(Fintype.card I : ℝ)^(k-1)+u := by
    intro i v
    have heq := monochromatic_copies_part_count R σ (fun e=>v∈R e) i
    have heq' : (Finset.univ.filter (fun e : E'=>e.1=i ∧ v∈R' e)).card=
        ((hypergraphColorClass R σ i).filter (fun e=>v∈R e)).card := by
      convert heq using 1 <;> congr 1 <;> ext e <;> simp only [R',Finset.mem_filter,Finset.mem_univ,true_and]
    rw [heq']
    by_cases hv : σ v=i
    · rw [hypergraphColorClass_degree R σ i v hv]
      have hh := (abs_lt.mp (hσdeg v i)).2
      have hdiv := div_le_div_of_nonneg_right (hdegree v)
        (show 0≤(Fintype.card I : ℝ)^(k-1) by positivity)
      linarith
    · rw [hypergraphColorClass_degree_zero R σ i v hv,Nat.cast_zero]
      exact add_nonneg (div_nonneg hd (by positivity)) hu
  have hcode' : ∀ i v z,v≠z →
      ((Finset.univ.filter (fun e : E'=>e.1=i ∧ v∈R' e ∧ z∈R' e)).card : ℝ)≤β := by
    intro i v z hvz
    have heq := monochromatic_copies_part_count R σ (fun e=>v∈R e ∧ z∈R e) i
    have heq' : (Finset.univ.filter (fun e : E'=>e.1=i ∧ v∈R' e ∧ z∈R' e)).card=
        ((hypergraphColorClass R σ i).filter (fun e=>v∈R e ∧ z∈R e)).card := by
      convert heq using 1 <;> congr 1 <;> ext e <;> simp only [R',Finset.mem_filter,Finset.mem_univ,true_and]
    rw [heq']
    have hc : ((hypergraphColorClass R σ i).filter (fun e=>v∈R e ∧ z∈R e)).card≤
        (Finset.univ.filter (fun e=>v∈R e ∧ z∈R e)).card := by
      apply Finset.card_le_card
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
    exact (Nat.cast_le.mpr hc).trans (hcodeg v z hvz)
  have hweight' : ∀ i a,(∑ e : E',if e.1=i then w' a e else 0)≤W a/(Fintype.card I : ℝ)^k+s a := by
    intro i a
    have heq : (∑ e : E',if e.1=i then w' a e else 0)=∑ e∈hypergraphColorClass R σ i,w a e := by
      convert monochromatic_copies_part_sum R σ (w a) i using 1 <;>
        apply Finset.sum_congr <;> try (ext e;simp only [Finset.mem_univ])
      intro e _;rfl
    rw [heq]
    have hh := (abs_lt.mp (hσweight a i)).2
    rw [htotal] at hh
    linarith
  obtain ⟨M,hM,hMw⟩ := hN D B ((le_max_right _ _).trans hD) hB V E' I C A R' Sigma.fst
    (fun e=>hsize e.2.val) hparts w' b (fun _ a=>W a/(Fintype.card I : ℝ)^k+s a)
    (d/(Fintype.card I : ℝ)^(k-1)+u) β (fun _ a=>T a) s₀ s₁ s₂ hb
    (fun a e=>hw a e.2.val)
    (by
      intro i v
      convert hdeg' i v using 1 <;> congr 2 <;> ext e <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    (by
      intro i v z hvz
      convert hcode' i v z hvz using 1 <;> congr 2 <;> ext e <;>
        simp only [Finset.mem_filter,Finset.mem_univ,true_and]) hβ
    (by
      intro i a
      convert hweight' i a using 1 <;> apply Finset.sum_congr rfl <;>
        intro e _ <;> split_ifs <;> rfl) hs₀ hs₁ hs₂ hedge t ht hselect
  have hne : ∀ e,(R e).Nonempty := fun e=>Finset.card_pos.mp (by rw [hsize];omega)
  obtain ⟨hproj,hprojsum⟩ := monochromatic_copies_matching_projection R σ hne M hM
  refine ⟨M.image (monochromaticProjection R σ),hproj,?_⟩
  intro a
  let p : ℝ := Fintype.card I
  let den : ℝ := (Fintype.card C : ℝ)*⌈(1+ε)*(D : ℝ)⌉₊
  have hp : 0<p := Nat.cast_pos.mpr Fintype.card_pos
  have hDpos : (0 : ℝ)<D := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0<1) ((le_max_left _ _).trans hD))
  have hden : 0<den := mul_pos (Nat.cast_pos.mpr Fintype.card_pos)
    (Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity)))
  have hsumerror : |(∑ e : E',w' a e)-W a/p^(k-1)|≤p*s a := by
    have heq : (∑ _i : I,W a/p^k)=W a/p^(k-1) := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      change p*(W a/p^k)=W a/p^(k-1)
      rw [show k=(k-1)+1 by omega,pow_succ]
      field_simp
      simp only [Nat.add_sub_cancel]
    have hetotal : (∑ e : E',w' a e)=∑ i,∑ e∈hypergraphColorClass R σ i,w a e := by
      convert monochromatic_copies_total_sum R σ (w a) using 1 <;>
        apply Finset.sum_congr <;> try (ext e;simp only [Finset.mem_univ])
      intro e _;rfl
    rw [hetotal,← heq,← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i,|(∑ e∈hypergraphColorClass R σ i,w a e)-W a/p^k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : I,s a := Finset.sum_le_sum (fun i _=>by simpa only [htotal] using (hσweight a i).le)
      _ = p*s a := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,p]
  rw [hprojsum]
  simp only [mul_assoc]
  change |(∑ e∈M,w' a e)-W a/(p^(k-1)*den)|<t a+p*s a/den
  rw [← div_div]
  calc
    _ = |((∑ e∈M,w' a e)-(∑ e : E',w' a e)/den)+
        ((∑ e : E',w' a e)-W a/p^(k-1))/den| := by congr 1;ring
    _ ≤ |(∑ e∈M,w' a e)-(∑ e : E',w' a e)/den|+
        |((∑ e : E',w' a e)-W a/p^(k-1))/den| := abs_add_le _ _
    _ < t a+p*s a/den := add_lt_add_of_lt_of_le (hMw a)
      (by rw [abs_div,abs_of_pos hden];exact div_le_div_of_nonneg_right hsumerror hden.le)

end Oberwolfach
