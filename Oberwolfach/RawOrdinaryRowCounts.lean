module

public import Oberwolfach.OrdinaryRowResources
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! Mixed ordinary neighbourhood counts under the original raw sampling
law, including empty root sets and roots outside the fixed row domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinaryRowResources_target (P:SimpleGraph V) (p:ℝ) (s:U→Color→ℝ) (j:Color)
    (S:Finset V) (J:Finset U) (z:V) (hz:∀ x∈S,P.Adj x z):
    (∏ e∈ordinaryRowResources S J z,rawWheelMarginal P (fun _=>p) s j e)=
      p^S.card*∏ u∈J,s u j:=by
  unfold ordinaryRowResources
  rw [Finset.prod_union (by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp he
    obtain ⟨b,hb,hf⟩:=Finset.mem_image.mp hf
    cases he.trans hf.symm)]
  rw [Finset.prod_image (by
    intro a ha b hb he
    have hh:=Sym2.eq_iff.mp (Sum.inl.inj he)
    rcases hh with hh|hh
    · exact hh.1
    · exact hh.1.trans hh.2)]
  rw [Finset.prod_image (by intro a ha b hb he;exact (Prod.mk.inj (Sum.inr.inj he)).2)]
  have hm (x:V) (hx:x∈S):rawWheelMarginal P (fun _=>p) s j (Sum.inl s(x,z))=p:=by
    simp [rawWheelMarginal,SimpleGraph.mem_edgeSet,hz x hx]
  rw [Finset.prod_congr rfl (fun x hx=>hm x hx),Finset.prod_const]
  rfl

theorem rawOrdinaryRowCount_patterns (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (j:Color) (A S:Finset V) (J:Finset U):
    rawOrdinaryPatternSum P π d (fun z:common A S (fun x=>P.neighborFinset x)=>ordinaryRowResources S J z.val)
      (fun _=>1) j σ=
    ((common (common A S (fun x=>(rawWheelGraph P σ).neighborFinset x)) J
      (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))).card:ℝ):=by
  let C:=common A S (fun x=>P.neighborFinset x)
  unfold rawOrdinaryPatternSum supportedPatternSum
  rw [Finset.sum_coe_sort C (fun z:V=>(1:ℝ)*patternValue (ordinaryRowResources S J z)
    (fun _=>true) (ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j)))]
  simp_rw [one_mul,patternValue_indicator]
  have heq:(∑ z∈C,if ∀ e∈ordinaryRowResources S J z,ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j) e=true then (1:ℝ) else 0)=
      ((C.filter (fun z=>∀ e∈ordinaryRowResources S J z,ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j) e=true)).card:ℝ):=by
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  trans ((C.filter (fun z=>∀ e∈ordinaryRowResources S J z,ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j) e=true)).card:ℝ)
  · convert heq using 1 <;> congr!
  congr 1
  apply congrArg Finset.card
  ext z
  simp only [C,Finset.mem_filter,mem_common_iff,Finset.mem_univ,true_and,
    ordinaryRowResources,Finset.forall_mem_union,Finset.forall_mem_image,
    ordinaryResourceState,Sum.elim_inl,Sum.elim_inr,decide_eq_true_eq,SimpleGraph.mem_edgeSet,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨hz,hp⟩,hr,hs⟩
    exact ⟨⟨hz,hr⟩,hs⟩
  · rintro ⟨⟨hz,hr⟩,hs⟩
    exact ⟨⟨hz,fun x hx=>(@hr x hx).1⟩,hr,hs⟩

theorem rawOrdinaryRowCount_tail (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (A:Finset V) (hA:A.Nonempty) (S:Finset V) (J:Finset U) (h:ℕ) (hsize:S.card+J.card≤h)
    (j:Color) (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|((common (common A S (fun x=>(rawWheelGraph P σ).neighborFinset x)) J
        (fun u=>Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u))).card:ℝ)-
        p^S.card*(∏ u∈J,s u j)*(common A S (fun x=>P.neighborFinset x)).card|)≤
      2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*((h:ℝ)+1)*A.card))):=by
  let C:=common A S (fun x=>P.neighborFinset x)
  have hh:=rawOrdinaryPatternSum_tail P π (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS hnoshort
    (fun z:C=>ordinaryRowResources S J z.val) (fun _=>1) (by intro _;norm_num)
    (fun z a ha b hb hab=>ordinaryRowResources_disjoint π d S J z.val a b ha hb hab) j
    2 ((h:ℝ)+1) A.card (by norm_num) (by positivity) (by exact_mod_cast hA.card_pos)
    (by
      intro z
      have hh:=(ordinaryRowResources_card S J z.val).trans hsize
      have hh':((ordinaryRowResources S J z.val).card:ℝ)≤h:=by exact_mod_cast hh
      linarith only [hh'])
    (by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Fintype.card_coe]
      apply Nat.cast_le.mpr
      exact Finset.card_le_card (fun z hz=>((mem_common_iff _ _ _ _).mp hz).1))
    (ordinaryRowResources_load S J C) t ht
  have he:(∑ z:C,(1:ℝ)*∏ e∈ordinaryRowResources S J z.val,rawWheelMarginal P (fun _=>p) s j e)=
    p^S.card*(∏ u∈J,s u j)*C.card:=by
    have hz (z:C):∀ x∈S,P.Adj x z.val:=by
      intro x hx
      exact (P.mem_neighborFinset _ _).mp (((mem_common_iff _ _ _ _).mp z.property).2 x hx)
    simp_rw [one_mul,ordinaryRowResources_target P p s j S J _ (hz _)]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    ring
  rw [he] at hh
  simpa only [rawOrdinaryRowCount_patterns,C] using hh

end Oberwolfach
