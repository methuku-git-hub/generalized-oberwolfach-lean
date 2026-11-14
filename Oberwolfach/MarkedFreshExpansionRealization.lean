module

public import Oberwolfach.MarkedExpansionRealization
public import Oberwolfach.MarkedFreshVertexMaps

@[expose] public section

/-! Embed an entire finite expansion on fresh host vertices, including its
old formal vertices. All choices and separation conditions are constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_fresh_expansion_realization
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (v₀:V) (W Z:Finset V) (B:Finset U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card V₀+Fintype.card (A⊕S)*(l+5)+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card U₀+Fintype.card (A⊕S)<ch):
    ∃ R:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega)) tail head ktail khead H₀ HK π b,
      Function.Injective R.rows∧Function.Injective R.hubs∧
      (∀ u,R.hubs u∉B)∧
      (∀ v,R.rows v∉W∧R.rows v∉Z∧∀ z∈Z,¬PermutationClose π b (R.rows v) z)∧
      PermutationSeparated π b R.rows:=by
  have horders:=marked_host_order_bounds Q v₀
  have hnon:0≤(Fintype.card (A⊕S):ℝ)*(l+5)+l+16:=by positivity
  have hbnon:0≤(2*b+1:ℝ):=by positivity
  have hbrow:(W.card:ℝ)+(Fintype.card V₀+Z.card)*(2*b+1)<c:=by
    nlinarith only [hbudget,mul_nonneg hnon hbnon]
  obtain ⟨f,hf,hfs⟩:=marked_fresh_row_map (I:=V₀) W Z horders.1 hbrow
  have hhub:B.card+Fintype.card U₀≤Fintype.card U:=by
    have hh:(B.card:ℝ)+Fintype.card U₀<(Fintype.card U:ℝ):=by
      have hnn:0≤(Fintype.card (A⊕S):ℝ):=by positivity
      linarith only [hB,horders.2,hnn]
    exact_mod_cast hh.le
  obtain ⟨g,hg⟩:=finite_fresh_hub_map (J:=U₀) B hhub
  let Z':=Z∪Finset.univ.image f
  let B':=B∪Finset.univ.image g
  have hZc:(Z'.card:ℝ)≤Z.card+Fintype.card V₀:=by
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le.trans (by simp)) _)
  have hBc:(B'.card:ℝ)≤B.card+Fintype.card U₀:=by
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_image_le.trans (by simp)) _)
  have hrow:(W.card:ℝ)+(Z'.card+Fintype.card (A⊕S)*(l+5)+l+16)*(2*b+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hZc hbnon
    nlinarith only [hh,hbudget]
  obtain ⟨R,hRi,hRhi,hold,holdh,hnewhub,hnew,hsep⟩:=marked_expansion_realization Q hl G f g
    f.injective g.injective W Z' B'
    (fun v=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))
    (fun u=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)) hp hrow
    (by linarith only [hBc,hB])
  refine ⟨R,hRi,hRhi,?_,?_,?_⟩
  · rintro (u|i)
    · rw [holdh];exact hg u
    · exact fun hu=>hnewhub i (Finset.mem_union_left _ hu)
  · rintro (v|⟨i,k⟩)
    · rw [hold];exact hf v
    · exact ⟨(hnew i k).1,fun hv=>(hnew i k).2.1 (Finset.mem_union_left _ hv),
        fun z hz=>(hnew i k).2.2 z (Finset.mem_union_left _ hz)⟩
  · rintro (v|⟨i,k⟩) (w|⟨j,k'⟩) hne
    · rw [hold,hold];exact hfs v w (fun he=>hne (congrArg Sum.inl he))
    · rw [hold]
      exact ((hnew j k').2.2 (f v) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))) ∘
        (permutationClose_symm π b _ _).mp
    · rw [hold]
      exact (hnew i k).2.2 (f w) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,Finset.mem_univ _,rfl⟩))
    · exact hsep i j k k' (fun he=>hne (congrArg Sum.inr he))

end Oberwolfach
