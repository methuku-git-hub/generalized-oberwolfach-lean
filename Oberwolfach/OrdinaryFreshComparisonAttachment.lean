module

public import Oberwolfach.OrdinaryFreshComparisonEmbedding
public import Oberwolfach.OrdinaryRelativeAttachmentRealization

@[expose] public section

/-! Embed the decomposable end of the ordinary absorber diagram. Both the
comparison wheels and their attached wheels are constructed in the actual host;
the result is wholly fresh and has an actual host-wheel decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem ordinary_fresh_comparison_attachment (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (B:Finset U) (r k:ℕ) (hr:3≤r)
    (ρ:I→OrdinaryComparisonRows r k) (d c cH:ℝ) (hd:0≤d)
    (hF:∀ v,(F.degree v:ℝ)≤d) (hA:c≤(A.card:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+k+k*r+Fintype.card I*r+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+k+Fintype.card I<cH) :
    ∃ (f:OrdinaryComparisonRows r k⊕(I×Fin r)↪V) (g:OrdinaryComparisonHubs k⊕I↪U),
      (∀ a,f a∈A∧f a∉W∧f a∉R∧∀ z∈R,¬F.Adj (f a) z)∧
      (∀ a,g a∉B)∧(∀ a b,¬F.Adj (f a) (f b))∧
      (∀ a b,(ordinaryAttachmentRim (ordinaryComparisonRim r k (by omega))
        (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).Adj a b→Q.Adj (f a) (f b))∧
      (∀ a b,ordinaryAttachmentSpokes (ordinaryComparisonSpokes r k (by omega))
        ⟨0,by omega⟩ ρ a b→H (f a) (g b))∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
        (ordinaryHostResources ((ordinaryAttachmentRim (ordinaryComparisonRim r k (by omega))
          (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).map f)
          (ordinaryMappedSpokes (ordinaryAttachmentSpokes (ordinaryComparisonSpokes r k (by omega))
            ⟨0,by omega⟩ ρ) f g)) := by
  have hd1:0≤d+1:=by linarith
  obtain ⟨φ,ψ,hφ,hψ,hφF,hG,hH,hdec⟩:=ordinary_fresh_comparison_embedding Q F H A W R B r k hr d c cH hd hF hA hcount hhub
    (by have hpos:0≤(Fintype.card I:ℝ)*r*(d+1):=by positivity
        nlinarith only [hbudget,hpos])
    (by have hpos:0≤(Fintype.card I:ℝ):=by positivity
        linarith only [hB,hpos])
  let R':=R∪Finset.univ.image φ
  let B':=B∪Finset.univ.image ψ
  have hRc:(R'.card:ℝ)≤R.card+k+k*r:=by
    have hcard:(Finset.univ.image φ).card≤k+k*r:=by
      apply Finset.card_image_le.trans
      simp [OrdinaryComparisonRows]
    have hsum: R'.card≤R.card+(k+k*r):=(Finset.card_union_le _ _).trans (Nat.add_le_add_left hcard _)
    exact_mod_cast (by omega : R'.card≤R.card+k+k*r)
  have hBc:(B'.card:ℝ)≤B.card+k:=by
    have hcard:(Finset.univ.image ψ).card≤k:=by
      apply Finset.card_image_le.trans
      simp [OrdinaryComparisonHubs]
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hcard _)
  obtain ⟨f,g,hf,hg,hpriv,hnewhub,hprivF,hQ,hH',he,hd',hextra⟩:=
    ordinary_relative_attachment_realization Q F H A W R' B' φ ψ
      (ordinaryComparisonRim r k (by omega)) (ordinaryComparisonSpokes r k (by omega)) ρ
      (fun a=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
      (fun a=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
      hG hH r hr d c cH hd hF hcount hhub
      (by have hm:=mul_le_mul_of_nonneg_right hRc hd1;nlinarith only [hbudget,hm])
      (by linarith only [hB,hBc])
  have hcross:∀ i w a,¬F.Adj (f (.inr (i,w))) (f (.inl a)):=by
    intro i w a
    rw [hf]
    exact (hpriv i w).2.2.2 (φ a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
  refine ⟨f,g,?_,?_,?_,hQ,hH',?_⟩
  · intro a
    cases a with
    | inl a=>rw [hf];exact hφ a
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
      cases b with
      | inl b=>rw [hf,hf];exact hφF a b
      | inr p=>exact fun h=>hcross p.1 p.2 a h.symm
    | inr p=>
      cases b with
      | inl b=>exact hcross p.1 p.2 b
      | inr q=>exact hprivF p.1 q.1 p.2 q.2
  · rw [he]
    exact resource_decomposition_union _ _ _ hdec hextra hd'

end Oberwolfach
