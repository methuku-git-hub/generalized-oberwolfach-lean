module

public import Oberwolfach.ScaledSetRowCodegrees
public import Oberwolfach.OrdinaryEndpointNormalisation
public import Oberwolfach.LocalExtensionCounts

@[expose] public section

/-! Successive row covers on a later free set X, using only the relative
counts on the original fixed domain A. Restriction loses at most |A\X|
candidates; the original normalization and reference order remain unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_domain_row_covers
    (r:ℕ) (hr:4≤r) (C₀ α ω p₀:ℝ) (hC₀:0≤C₀)
    (hα:0<α) (hω:0<ω) (hp₀:0<p₀) (hp₀1:p₀≤1) :
    ∃ K:ℕ,0<K ∧ ∃ θ ε₀:ℝ,0<θ ∧ 0<ε₀ ∧ ∀ d:ℕ,∃ N:ℕ,
      ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (P Q F:SimpleGraph V) (H:V→U→Prop) (n:ℕ) (x:Fin n→V) (A X:Finset V) (q p ε:ℝ),
      N≤A.card → (n:ℝ)≤θ*A.card → ω*A.card≤(Fintype.card U:ℝ) →
      (Fintype.card U:ℝ)≤C₀*A.card → p₀≤q → p₀≤p → p≤1 → 0≤ε → ε≤ε₀ →
      Function.Injective x → X⊆A → (∀ i,x i∉X) → Q≤P →
      ((A\X).card:ℝ)≤p₀^6*(min α 1)*A.card/8 →
      (∀ i,Q.neighborFinset (x i)⊆X) →
      (∀ i,Q.degree (x i)=2*(Finset.univ.filter (H (x i))).card) →
      (∀ a,F.degree a≤d) → (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
      (∀ a,(1/2+α)*A.card≤((A∩P.neighborFinset a).card:ℝ)) →
      (∀ S:Finset V,∀ J:Finset U,S.card≤2 → J.card≤1 →
        |((common (common A S (fun v=>Q.neighborFinset v)) J
          (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
          q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card) →
      (∀ S:Finset V,S.card≤3 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
        |((common Finset.univ S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*Fintype.card U|≤ε*Fintype.card U) →
      ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
        (∀ i,OrdinaryRowCover (C i) (x i) X K) ∧
        (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈X,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
        (∀ a∈X,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r) := by
  let γ:=min α 1
  let β:=p₀^6*γ/4
  let κ:=p₀*ω/2
  have hγ:0<γ:=lt_min hα (by norm_num)
  have hγ1:γ≤1:=min_le_right _ _
  have hγα:γ≤α:=min_le_left _ _
  have hβ:0<β:=by dsimp [β];positivity
  have hκ:0<κ:=by dsimp [κ];positivity
  obtain ⟨K,hK,θ,e,hθ,he,hcover⟩:=ordinary_scaled_set_row_covers_from_codegrees r hr C₀ (β/2) κ p₀ hC₀ (by positivity) hκ hp₀
  let ε₀:=min (p₀/2) (min (e*p₀/4) (min (p₀*κ/2) β))
  have hε₀:0<ε₀:=by dsimp [ε₀];positivity
  refine ⟨K,hK,θ,ε₀,hθ,hε₀,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hcover d
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P Q F H n x A X q p ε hn hnθ hmlo hmhi hq hp hp1 hε hεsmall
    hx hXA hxA hQP hmissing hSA hbal hF hFx hdeg hrow hindex
  let T:=fun i=>Finset.univ.filter (H (x i))
  have he₁:ε≤p₀/2:=hεsmall.trans (min_le_left _ _)
  have he₂:4*ε≤e*p₀:=by
    have hh:=hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hh]
  have he₃:2*ε≤p₀*κ:=by
    have hh:=hεsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    linarith only [hh]
  have he₄:ε≤β:=hεsmall.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hS (i:Fin n):A∩Q.neighborFinset (x i)=Q.neighborFinset (x i):=Finset.inter_eq_right.mpr ((hSA i).trans hXA)
  have hsize (i:Fin n):|(T i).card-p*Fintype.card U|≤ε*Fintype.card U:=by
    have hh:=hindex {x i} (by simp) (by intros v hv w hw;simp only [Finset.mem_singleton] at hv hw;subst v;subst w;exact F.loopless.irrefl _)
    have heq:common Finset.univ ({x i}:Finset V) (fun v=>Finset.univ.filter (H v))=T i:=by
      ext u;simp [mem_common_iff,T]
    simpa only [heq,Finset.card_singleton,pow_one] using hh
  have hTlo (i:Fin n):κ*A.card≤((T i).card:ℝ):=by
    have hh:=(endpoint_spoke_normalisation (T i).card (Fintype.card U) 0 p p₀ ε e
      (Nat.cast_nonneg _) hp₀ hp hp1 hε he.le he₁ he₂ (hsize i)).1
    have hm:=mul_le_mul_of_nonneg_left hmlo hp₀.le
    dsimp [κ];nlinarith only [hh,hm]
  have hnorm (i:Fin n):=ordinary_endpoint_counts_normalised P Q F H A Finset.univ (x i) q p p₀ ε e
    hQP (hFx i) hp₀ hp hp1 hε he.le he₁ he₂
    (by simpa only [hS i,SimpleGraph.card_neighborFinset_eq_degree] using hbal i)
    (by
      have hh:=mul_le_mul_of_nonneg_right he₃ (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
      have ht:=mul_le_mul_of_nonneg_left (hTlo i) hp₀.le
      have hp':=mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (T i).card : (0:ℝ)≤(T i).card)
      nlinarith only [hh,ht,hp'])
    (fun S J hS hJ=>hrow S J (by omega) hJ)
    (by intro S hS hI;simpa only [Finset.card_univ] using hindex S hS hI)
  apply hN V U Q F H n x X A.card p hn hnθ hp hp1 hx hxA hSA hTlo
    (fun i=>(Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (by simpa only [Finset.card_univ] using hmhi))
    hbal hF hFx
  · intro i a ha
    have hh:=(hnorm i).2.1 a (by rw [hS i];exact (Q.mem_neighborFinset _ _).mpr ha)
    exact hh
  · intro i u hu
    have hh:=(hnorm i).2.2.1 u (Finset.mem_univ _)
    simpa only [hS i] using hh
  · intro i a b ha hb hab hfab
    exact (hnorm i).2.2.2 a (by rw [hS i];exact (Q.mem_neighborFinset _ _).mpr ha)
      b (by rw [hS i];exact (Q.mem_neighborFinset _ _).mpr hb) hab hfab
  · intro i u hu a hax c hcx
    let S:Finset V:={a,c}
    let J:Finset U:={u}
    have hs:S.card≤2:=by
      have hh:=Finset.card_insert_le a ({c}:Finset V)
      simpa only [Finset.card_singleton] using hh
    have hj:J.card≤2:=by simp [J]
    have hrel:=hrow S J hs (by simp [J])
    have hcount:=extension_relative_row_lower P Q ⊥ A S J
      (fun u=>Finset.univ.filter (fun v=>H v u)) 2 γ p₀ q p ε 0
      (by norm_num) (by norm_num) hγ hγ1 hp₀ hp₀1 hq hp (by norm_num) hs hj
      (by simp only [mul_zero];positivity) he₄
      (by intro v hv;norm_num;exact (mul_le_mul_of_nonneg_right (by linarith only [hγα]) (Nat.cast_nonneg A.card)).trans (hdeg v))
      (by intro v hv;simp)
      (by
        have hh:q^S.card*p^J.card*(common A S (fun v=>P.neighborFinset v)).card-ε*A.card≤
          ((common (common A S (fun v=>Q.neighborFinset v)) J (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ):=by
            linarith only [(abs_le.mp hrel).1]
        convert hh using 1 <;> congr! <;> ext v w <;> simp)
    have heq:common (common A S (fun v=>Q.neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>H v u))=
        (A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c:=by
      ext z;simp [mem_common_iff,S,J];tauto
    have hfull:β*A.card≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ):=by
      simpa only [heq] using hcount
    have hsub:((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c)⊆
        ((X.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c)∪(A\X):=by
      intro z hz
      have hh:=Finset.mem_inter.mp hz
      have hzA: z∈A:=(Finset.mem_filter.mp (Finset.mem_inter.mp hh.1).1).1
      by_cases hzX:z∈X
      · apply Finset.mem_union_left
        exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
          ⟨hzX,(Finset.mem_filter.mp (Finset.mem_inter.mp hh.1).1).2⟩,(Finset.mem_inter.mp hh.1).2⟩,hh.2⟩
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzA,hzX⟩)
    have hcard:((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card≤
        ((X.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card+(A\X).card:=
      (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcard':(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)≤
        ((X.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card+(A\X).card:=by exact_mod_cast hcard
    have hm:((A\X).card:ℝ)≤β*A.card/2:=by dsimp [β,γ];nlinarith only [hmissing]
    nlinarith only [hfull,hcard',hm]

end Oberwolfach
