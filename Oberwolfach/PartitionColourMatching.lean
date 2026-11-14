module

public import Oberwolfach.NearOptimalEdgeColouring
public import Oberwolfach.ColorClassLottery

@[expose] public section

/-! Proper edge colourings of the random edge parts are assembled into one
matching on vertex-disjoint parts. Every prescribed weight is controlled on
the same choice of colour classes. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem subtype_filter_card_eq {E : Type*} [Fintype E]
    (P Q : E → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun e : {e // P e}=>Q e.val)).card=
      (Finset.univ.filter (fun e=>P e ∧ Q e)).card := by
  classical
  apply Finset.card_bij (fun e _=>e.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.property,(Finset.mem_filter.mp he).2⟩
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro e he
    have h := (Finset.mem_filter.mp he).2
    exact ⟨⟨e,h.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩,rfl⟩

theorem partition_colouring_weighted_matching
    (k : ℕ) (hk : 0<k) (ε δ : ℝ) (hε : 0<ε) (hε1 : ε≤1/2)
    (hδ : 0<δ) (hδ1 : δ≤1) :
    ∃ D₀ : ℕ, ∀ D B : ℕ, D₀≤D → (B : ℝ)≤(D : ℝ)^(1-δ) →
      ∀ (V E I J T : Type) [Fintype V] [Fintype E] [Fintype I] [Fintype J] [Fintype T]
        [Nonempty J],
      ∀ (R : E → Finset V) (part : E → I) (split : E → J),
      (∀ e,(R e).card=k) →
      (∀ e f,part e≠part f → Disjoint (R e) (R f)) →
      (∀ i j v,(Finset.univ.filter (fun e=>part e=i ∧ split e=j ∧ v∈R e)).card≤D) →
      (∀ i j v u,v≠u →
        (Finset.univ.filter (fun e=>part e=i ∧ split e=j ∧ v∈R e ∧ u∈R e)).card≤B) →
      ∀ (w : T → E → ℝ) (b : T → I → ℝ) (t : T → ℝ),
      (∀ a e,0≤w a e) →
      (∀ a i j,(∑ e,if part e=i ∧ split e=j then w a e else 0)≤b a i) →
      (∀ a,0≤t a) →
      (∑ a,2*Real.exp (-2*(t a)^2/(∑ i,(b a i)^2)))<1 →
      ∃ M : Finset E,
        (∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
        ∀ a,|(∑ e∈M,w a e)-(∑ e,w a e)/
          ((Fintype.card J : ℝ)*⌈(1+ε)*(D : ℝ)⌉₊)|<t a := by
  classical
  obtain ⟨N,hNpos,hN⟩ := near_optimal_hypergraph_edge_colouring k hk ε δ hε hε1 hδ hδ1
  refine ⟨N,?_⟩
  intro D B hD hB V E I J T _ _ _ _ _ _ R part split hsize hparts hdegree hcodeg w b t hw hb ht hsmall
  let l := ⌈(1+ε)*(D : ℝ)⌉₊
  have hl : 0<l := by
    have hDR : (0 : ℝ)<D := Nat.cast_pos.mpr (lt_of_lt_of_le (by omega : 0<N) hD)
    exact Nat.ceil_pos.mpr (by positivity)
  letI : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp hl
  have hcells : ∀ ij : I×J,∃ f : {e // part e=ij.1 ∧ split e=ij.2} → Fin l,
      ∀ e g,(hypergraphLineGraph (fun e : {e // part e=ij.1 ∧ split e=ij.2}=>R e.val)).Adj e g → f e≠f g := by
    intro ij
    apply hN D B hD hB V {e // part e=ij.1 ∧ split e=ij.2} (fun e=>R e.val) (fun e=>hsize e.val)
    · intro v
      have heq := subtype_filter_card_eq (fun e=>part e=ij.1 ∧ split e=ij.2) (fun e=>v∈R e)
      change (Finset.univ.filter (fun e : {e // part e=ij.1 ∧ split e=ij.2}=>v∈R e.val)).card≤D
      have heq' : (Finset.univ.filter (fun e : {e // part e=ij.1 ∧ split e=ij.2}=>v∈R e.val)).card=
          (Finset.univ.filter (fun e=>part e=ij.1 ∧ split e=ij.2 ∧ v∈R e)).card := by
        convert heq using 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_assoc]
      rw [heq']
      convert hdegree ij.1 ij.2 v using 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter,and_assoc]
    · intro v u hvu
      have heq := subtype_filter_card_eq (fun e=>part e=ij.1 ∧ split e=ij.2) (fun e=>v∈R e ∧ u∈R e)
      have heq' : (Finset.univ.filter (fun e : {e // part e=ij.1 ∧ split e=ij.2}=>v∈R e.val ∧ u∈R e.val)).card=
          (Finset.univ.filter (fun e=>part e=ij.1 ∧ split e=ij.2 ∧ v∈R e ∧ u∈R e)).card := by
        convert heq using 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_assoc]
      rw [heq']
      convert hcodeg ij.1 ij.2 v u hvu using 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter,and_assoc]
  choose χ hχ using hcells
  let color (e : E) : J×Fin l := (split e,χ (part e,split e) ⟨e,rfl,rfl⟩)
  have hcolor : ∀ e f,e≠f → part e=part f → color e=color f → Disjoint (R e) (R f) := by
    intro e f hef hp hc
    have hs : split e=split f := congrArg Prod.fst hc
    let e' : {g // part g=part e ∧ split g=split e} := ⟨e,rfl,rfl⟩
    let f' : {g // part g=part e ∧ split g=split e} := ⟨f,hp.symm,hs.symm⟩
    have htransport (i : I) (j : J) (g : E) (hpi : part g=i) (hsj : split g=j) :
        χ (part g,split g) ⟨g,rfl,rfl⟩=χ (i,j) ⟨g,hpi,hsj⟩ := by
      subst i;subst j;rfl
    have hχeq : χ (part e,split e) e'=χ (part e,split e) f' :=
      (congrArg Prod.snd hc).trans (htransport _ _ f hp.symm hs.symm)
    by_contra hn
    exact hχ (part e,split e) e' f' ⟨fun h=>hef (congrArg Subtype.val h),hn⟩ hχeq
  have hweight : ∀ a i c,colorClassWeight part color (w a) i c≤b a i := by
    intro a i c
    apply (Finset.sum_le_sum (fun e _=>show
      (if part e=i ∧ color e=c then w a e else 0)≤
      (if part e=i ∧ split e=c.1 then w a e else 0) from ?_)).trans (hb a i c.1)
    by_cases h : part e=i ∧ color e=c
    · have hh : part e=i ∧ split e=c.1 := ⟨h.1,congrArg Prod.fst h.2⟩
      rw [if_pos h,if_pos hh]
    · rw [if_neg h]
      split_ifs
      · exact hw a e
      · exact le_refl _
  obtain ⟨M,hM,hMw⟩ := colorClassLottery_matching R part color hparts hcolor
    Finset.univ w b t (fun a _=>hw a) (fun a _=>hweight a) (fun a _=>ht a)
    (by simpa using hsmall)
  refine ⟨M,hM,?_⟩
  intro a
  simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using hMw a (Finset.mem_univ _)

end Oberwolfach
