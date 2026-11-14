module

public import Oberwolfach.OrdinaryFreshRootLabels
public import Oberwolfach.OrdinaryRelativeAttachmentEmbedding
public import Oberwolfach.OrdinaryComparisonFromDivisibility
public import Oberwolfach.OrdinaryAttachmentHostDecomposition

@[expose] public section

/-! The decomposable comparison graph is embedded using actual wheels
of the relative host. All its row labels are mutually separated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_fresh_comparison_embedding (Q F:SimpleGraph V) (H:V→U→Prop)
    (A W R:Finset V) (B:Finset U) (r k:ℕ) (hr:3≤r) (d c cH:ℝ) (hd:0≤d)
    (hF:∀ v,(F.degree v:ℝ)≤d) (hA:c≤(A.card:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+k+k*r+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+k<cH) :
    ∃ (f:OrdinaryComparisonRows r k↪V) (g:OrdinaryComparisonHubs k↪U),
      (∀ a,f a∈A ∧ f a∉W ∧ f a∉R ∧ ∀ z∈R,¬F.Adj (f a) z) ∧
      (∀ a,g a∉B) ∧ (∀ a b,¬F.Adj (f a) (f b)) ∧
      (∀ a b,(ordinaryComparisonRim r k (by omega)).Adj a b→Q.Adj (f a) (f b)) ∧
      (∀ a b,ordinaryComparisonSpokes r k (by omega) a b→H (f a) (g b)) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
        (ordinaryHostResources ((ordinaryComparisonRim r k (by omega)).map f)
          (ordinaryMappedSpokes (ordinaryComparisonSpokes r k (by omega)) f g)) := by
  have hd1:0≤d+1:=by linarith
  obtain ⟨φ,hφ,hφF,hφR⟩:=exists_separated_row_embedding (Fin k) F A W R d hd hF (by
    simp only [Fintype.card_fin]
    have hm:0≤((k:ℝ)*r+r+6)*(d+1):=by positivity
    nlinarith only [hbudget,hA,hm])
  let ψ:Empty↪U:=⟨Empty.elim,fun a=>a.elim⟩
  let R':=R∪Finset.univ.image φ
  have hRc:(R'.card:ℝ)≤R.card+k:=by
    have hh: (Finset.univ.image φ).card≤k:=Finset.card_image_le.trans (by simp)
    exact_mod_cast (Finset.card_union_le R (Finset.univ.image φ)).trans (Nat.add_le_add_left hh R.card)
  obtain ⟨f,g,hf,hg,hpriv,hnewhub,hprivF,hQ,hH⟩:=ordinary_relative_attachment_embedding Q F H A W R' B φ ψ
    ⊥ (fun (_:Fin k) (_:Empty)=>False) id
    (fun a=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
    (fun a=>a.elim) (fun a b h=>h.elim) (fun a b h=>h.elim)
    r hr d c cH hd hF hcount hhub
    (by simp only [Fintype.card_fin];have hm:=mul_le_mul_of_nonneg_right hRc hd1;nlinarith only [hbudget,hm])
    (by simpa only [Fintype.card_fin] using hB)
  have hcross:∀ i w a,¬F.Adj (f (.inr (i,w))) (f (.inl a)):=by
    intro i w a
    rw [hf]
    exact (hpriv i w).2.2.2 (φ a) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩))
  have hind:∀ a b,¬F.Adj (f a) (f b):=by
    intro a b
    cases a with
    | inl a=>
      cases b with
      | inl b=>rw [hf,hf];exact hφF a b
      | inr p=>exact fun h=>hcross p.1 p.2 a h.symm
    | inr p=>
      cases b with
      | inl b=>exact hcross p.1 p.2 b
      | inr q=>exact hprivF p.1 q.1 p.2 q.2
  have hC:IsEmbeddedCycle (SimpleGraph.cycleGraph r) r:=by
    refine ⟨hr,Function.Embedding.refl _,?_⟩
    change SimpleGraph.cycleGraph r=(SimpleGraph.cycleGraph r).map id
    rw [SimpleGraph.map_id]
  have hfull:∀ w:Fin r,w∈(SimpleGraph.cycleGraph r).support:=by
    intro w;rw [cycleGraph_support_eq_univ hr];exact Set.mem_univ _
  have hdec:=ordinary_attachment_extra_host_decomposition Q F H (SimpleGraph.cycleGraph r) hC hfull
    ⟨0,by omega⟩ (id:Fin k→Fin k) f g hQ hH hcross hprivF
  refine ⟨f,g,?_,?_,hind,hQ,hH,hdec⟩
  · intro a
    cases a with
    | inl a=>rw [hf];exact ⟨(hφ a).1,(hφ a).2.1,(hφ a).2.2,hφR a⟩
    | inr p=>exact ⟨(hpriv p.1 p.2).1,(hpriv p.1 p.2).2.1,
        fun h=>(hpriv p.1 p.2).2.2.1 (Finset.mem_union_left _ h),
        fun z hz=>(hpriv p.1 p.2).2.2.2 z (Finset.mem_union_left _ hz)⟩
  · intro a
    cases a with
    | inl a=>exact a.elim
    | inr i=>exact hnewhub i

end Oberwolfach
