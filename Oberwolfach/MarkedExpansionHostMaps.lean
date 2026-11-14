module

public import Oberwolfach.MarkedExpansionWheelFamilies
public import Oberwolfach.IndexedMarkedExpansionSimplicity
public import Oberwolfach.MarkedPaddedTypedPresence

@[expose] public section

/-! Actual vertex maps for an indexed expansion. Old incidences are crossed
with the displayed private wheels; every resulting incidence is in the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

def markedExpansionHostRows (f:V₀→V)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK):
    V₀⊕((A⊕S)×Fin (l+5))→V:=Sum.elim f (fun p=>(C p.1).1.val p.2)

def markedExpansionHostHubs (g:U₀→U)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK):
    U₀⊕(A⊕S)→U:=Sum.elim g (fun i=>(C i).2.val)

theorem marked_expansion_host_rows_injective (f:V₀→V)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hf:Function.Injective f) (Z:Finset V) (hfZ:∀ v,f v∈Z)
    (hnew:∀ i k,(C i).1.val k∉Z)
    (hsep:∀ i j k k',((i,k):(A⊕S)×Fin (l+5))≠(j,k')→
      ¬PermutationClose π b ((C i).1.val k) ((C j).1.val k')):
    Function.Injective (markedExpansionHostRows f C):=by
  rintro (v|⟨i,k⟩) (w|⟨j,k'⟩) he
  · exact congrArg Sum.inl (hf he)
  · change f v=(C j).1.val k' at he
    exact False.elim (hnew j k' (he ▸ hfZ v))
  · change (C i).1.val k=f w at he
    exact False.elim (hnew i k (he.symm ▸ hfZ w))
  · apply congrArg Sum.inr
    by_contra hne
    exact hsep i j k k' hne (Or.inl he)

theorem marked_expansion_host_hubs_injective (g:U₀→U)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hg:Function.Injective g) (B:Finset U) (hgB:∀ u,g u∈B)
    (hnew:∀ i,(C i).2.val∉B) (hC:Function.Injective (fun i=>(C i).2.val)):
    Function.Injective (markedExpansionHostHubs g C):=by
  rintro (u|i) (v|j) he
  · exact congrArg Sum.inl (hg he)
  · change g u=(C j).2.val at he
    exact False.elim (hnew j (he ▸ hgB u))
  · change (C i).2.val=g v at he
    exact False.elim (hnew i (he.symm ▸ hgB v))
  · exact congrArg Sum.inr (hC he)

theorem marked_expansion_host_present (G:IndexedMarkedGraph V₀ U₀ A S)
    (f:V₀→V) (g:U₀→U)
    (C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
    (hC:∀ i,MarkedExpansionWheelConditions (f∘G.src) (f∘G.dst) (f∘G.row) (g∘G.hub) G.jr G.js i (C i)):
    let D:=indexedMarkedExpansion G (l+4) (by omega)
    let F:=markedExpansionHostRows f C
    let H:=markedExpansionHostHubs g C
    (∀ a,markedArcPresent tail head ktail khead (D.jr a) (F (D.src a)) (F (D.dst a)))∧
    (∀ s,if D.js s then HK (F (D.row s)) (H (D.hub s)) else H₀ (F (D.row s)) (H (D.hub s))):=by
  dsimp only
  constructor
  · rintro (a|⟨a|s,k⟩)
    · exact (hC (.inl a)).1
    · change markedArcPresent tail head ktail khead (decide (k=Fin.last (l+4)))
        ((C (.inl a)).1.val k) (markedExpansionHostRows f C ((indexedMarkedExpansion G (l+4) (by omega)).dst (.inr (.inl a,k))))
      rw [indexedMarkedExpansion_dst_private_rim]
      by_cases hk:k=markedExpansionRimPosition (l+4) (by omega) (G.jr a)
      · rw [if_pos hk,hk,markedExpansionRimPosition_type]
        exact (hC (.inl a)).2
      · rw [if_neg hk]
        simpa only [markedExpansionHostRows,Sum.elim_inr,markedArcPresent,decide_eq_true_eq] using
          marked_cycle_canonical_typed_presence (C (.inl a)).1 k
    · change markedArcPresent tail head ktail khead (decide (k=Fin.last (l+4)))
        ((C (.inr s)).1.val k) ((C (.inr s)).1.val (finRotate (l+5) k))
      simpa only [markedArcPresent,decide_eq_true_eq] using
        marked_cycle_canonical_typed_presence (C (.inr s)).1 k
  · rintro (s|⟨a|s,k⟩)
    · exact (hC (.inr s)).1
    · change if decide (k=0) then HK ((C (.inl a)).1.val k) (C (.inl a)).2.val
        else H₀ ((C (.inl a)).1.val k) (C (.inl a)).2.val
      simpa only [decide_eq_true_eq] using marked_wheel_canonical_spoke_presence (C (.inl a)) k
    · change if decide (k=0) then HK ((C (.inr s)).1.val k)
        (markedExpansionHostHubs g C ((indexedMarkedExpansion G (l+4) (by omega)).hub (.inr (.inr s,k))))
        else H₀ ((C (.inr s)).1.val k)
        (markedExpansionHostHubs g C ((indexedMarkedExpansion G (l+4) (by omega)).hub (.inr (.inr s,k))))
      rw [indexedMarkedExpansion_hub_private_spoke]
      by_cases hk:k=markedExpansionSpokePosition (l+4) (by omega) (G.js s)
      · rw [if_pos hk,hk,markedExpansionSpokePosition_type]
        exact (hC (.inr s)).2
      · rw [if_neg hk]
        simpa only [markedExpansionHostHubs,Sum.elim_inr,decide_eq_true_eq] using
          marked_wheel_canonical_spoke_presence (C (.inr s)) k

end Oberwolfach
