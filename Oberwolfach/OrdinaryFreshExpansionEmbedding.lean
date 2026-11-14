module

public import Oberwolfach.OrdinaryFreshRootLabels
public import Oberwolfach.OrdinaryRelativeExpansionEmbedding

@[expose] public section

/-! Embed a wholly new finite expansion, including its old-label copies.
Every row lies in A, avoids W and R, and is separated from R and every
other row. Thus adjacent expansions can serve as disjoint transformer roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E J : Type} [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U]
    [Fintype E] [Fintype J] [DecidableEq V] [DecidableEq U]

theorem ordinary_fresh_expansion_embedding (Q F : SimpleGraph V) (H : V→U→Prop)
    (A W R:Finset V) (B:Finset U) (x y:E→V₀) (v:J→V₀) (u:J→U₀)
    (r:ℕ) (hr:3≤r) (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hA:c≤(A.card:ℝ)) (hU:cH≤(Fintype.card U:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair:∀ a b v w,c≤(((A.filter (fun z=>H z a∧H z b))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+Fintype.card V₀+Fintype.card (E⊕J)*r+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+Fintype.card U₀+Fintype.card (E⊕J)<cH) :
    ∃ (f:ExpansionRow V₀ E J (Fin r)↪V) (g:ExpansionHub U₀ E J↪U),
      (∀ a,f a∈A ∧ f a∉W ∧ f a∉R ∧ ∀ z∈R,¬F.Adj (f a) z) ∧
      (∀ a,g a∉B) ∧ (∀ a b,¬F.Adj (f a) (f b)) ∧
      (∀ a b,(ordinaryExpansionRim (J:=J) (SimpleGraph.cycleGraph r)
        ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y).Adj a b→Q.Adj (f a) (f b)) ∧
      (∀ a b,ordinaryExpansionSpokes (E:=E) ⟨0,by omega⟩ v u a b→H (f a) (g b)) := by
  have hd1:0≤d+1:=by linarith
  obtain ⟨φ,hφ,hφF,hφR⟩ := exists_separated_row_embedding V₀ F A W R d hd hF (by
    have hh:0≤(Fintype.card (E⊕J):ℝ)*r+r+6:=by positivity
    have hm:=mul_nonneg hh hd1
    nlinarith only [hbudget,hA,hm])
  obtain ⟨ψ,hψ⟩ := exists_fresh_hub_embedding U₀ B (by
    have hh:(B.card:ℝ)+Fintype.card U₀≤Fintype.card U:=by
      have hn:0≤(Fintype.card (E⊕J):ℝ):=by positivity
      linarith only [hB,hU,hn]
    exact_mod_cast hh)
  let R':=R∪Finset.univ.image φ
  let B':=B∪Finset.univ.image ψ
  have hRc:(R'.card:ℝ)≤R.card+Fintype.card V₀:=by
    exact_mod_cast (Finset.card_union_le R (Finset.univ.image φ)).trans (Nat.add_le_add_left
      ((Finset.card_image_le).trans_eq Finset.card_univ) R.card)
  have hBc:(B'.card:ℝ)≤B.card+Fintype.card U₀:=by
    exact_mod_cast (Finset.card_union_le B (Finset.univ.image ψ)).trans (Nat.add_le_add_left
      ((Finset.card_image_le).trans_eq Finset.card_univ) B.card)
  obtain ⟨f,g,hf,hg,hpriv,hnewhub,hprivF,hQ,hH⟩ := ordinary_relative_expansion_embedding Q F H A W R' B' φ ψ x y v u
    (fun a=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
    (fun a=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
    r hr d c cH hd hF hcount hpair hhub
    (by have hm:=mul_le_mul_of_nonneg_right hRc hd1;nlinarith only [hbudget,hm])
    (by linarith only [hB,hBc])
  refine ⟨f,g,?_,?_,?_,hQ,hH⟩
  · intro a
    cases a with
    | inl a=>rw [hf];exact ⟨(hφ a).1,(hφ a).2.1,(hφ a).2.2,hφR a⟩
    | inr p=>exact ⟨(hpriv p.1 p.2).1,(hpriv p.1 p.2).2.1,
        fun h=>(hpriv p.1 p.2).2.2.1 (Finset.mem_union_left _ h),
        fun z hz=>(hpriv p.1 p.2).2.2.2 z (Finset.mem_union_left _ hz)⟩
  · intro a
    cases a with
    | inl a=>rw [hg];exact hψ a
    | inr i=>exact fun h=>hnewhub i (Finset.mem_union_left _ h)
  · intro a b
    cases a with
    | inl a=>
      rw [hf]
      cases b with
      | inl b=>rw [hf];exact hφF a b
      | inr p=>
        exact fun h=>(hpriv p.1 p.2).2.2.2 (φ a)
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)) h.symm
    | inr p=>
      cases b with
      | inl b=>
        rw [hf]
        exact (hpriv p.1 p.2).2.2.2 (φ b)
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩))
      | inr q=>exact hprivF p.1 q.1 p.2 q.2

end Oberwolfach
