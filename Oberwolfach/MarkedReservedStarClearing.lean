module

public import Oberwolfach.MarkedOldInnerAgreement
public import Oberwolfach.MarkedActualRowResources

@[expose] public section

/-! The exact inner-star identity after reserving the corrected inner
star and covering the prescribed correction. It implies the support
conditions used by the subsequent deep-row and deep-hub constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [DecidableEq V] [DecidableEq U]

theorem marked_reserved_star_clearing
    (R D FE:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hD:D⊆R.filter (markedInnerResource I J))
    (hFE:FE.filter (markedInnerResource I J)=D.filter (markedStarResource T W)):
    let C:=R.filter (markedInnerResource I J)
    let K:=(C\D).filter (markedStarResource T W)
    let Q:=R\K
    (Q.filter (markedInnerResource I J)).filter (markedStarResource T W)=D.filter (markedStarResource T W)∧
    ((Q\FE).filter (markedInnerResource I J)).filter (markedStarResource T W)=∅:=by
  have hident:((R\((R.filter (markedInnerResource I J)\D).filter (markedStarResource T W))).filter
      (markedInnerResource I J)).filter (markedStarResource T W)=D.filter (markedStarResource T W):=by
    ext e
    have hd:e∈D→e∈R∧markedInnerResource I J e:=fun he=>Finset.mem_filter.mp (hD he)
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  refine ⟨hident,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have he1:=Finset.mem_filter.mp he
  have he2:=Finset.mem_filter.mp he1.1
  obtain ⟨hq,hn⟩:=Finset.mem_sdiff.mp he2.1
  have hi:=he2.2
  have hs:=he1.2
  have hd:e∈D.filter (markedStarResource T W):=by
    rw [←hident]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hq,hi⟩,hs⟩
  rw [←hFE] at hd
  exact hn (Finset.mem_filter.mp hd).1

theorem marked_cleared_star_neighbours
    {E K:Type} [Fintype E] [Fintype K] [Fintype V] [Fintype U]
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (R:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hTI:T⊆I) (hWJ:W⊆J) (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (hR:∀ a:E⊕K,Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈R)
    (hS:∀ x u,H₀ x u∨HK x u→Sum.inr (x,u)∈R)
    (hclear:(R.filter (markedInnerResource I J)).filter (markedStarResource T W)=∅):
    (∀ a:E⊕K,Sum.elim head khead a∈T→Sum.elim tail ktail a∉I)∧
    (∀ a:E⊕K,Sum.elim tail ktail a∈T→Sum.elim head khead a∉I)∧
    (∀ x∈T,∀ u,H₀ x u∨HK x u→u∉J)∧
    (∀ u∈W,∀ x,H₀ x u∨HK x u→x∉I):=by
  have hn (r:Finset V⊕(V×U)) (hr:r∈R) (hi:markedInnerResource I J r)
      (hs:markedStarResource T W r):False:=by
    have hh:=Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hr,hi⟩,hs⟩
    rw [hclear] at hh
    exact Finset.notMem_empty r hh
  refine ⟨?_,?_,?_,?_⟩
  · intro a ha hi
    exact hn _ (hR a) ((marked_physical_edge_inner_iff I hI a).mpr ⟨hi,hTI ha⟩)
      ((marked_physical_rim_star_iff tail head ktail khead π T W hT a).mpr (Or.inr ha))
  · intro a ha hi
    exact hn _ (hR a) ((marked_physical_edge_inner_iff I hI a).mpr ⟨hTI ha,hi⟩)
      ((marked_physical_rim_star_iff tail head ktail khead π T W hT a).mpr (Or.inl ha))
  · intro x hx u hu hJ
    exact hn _ (hS x u hu) ⟨hTI hx,hJ⟩ (Or.inl hx)
  · intro u hu x hx hI'
    exact hn _ (hS x u hx) ⟨hI',hWJ hu⟩ (Or.inr hu)

end Oberwolfach
