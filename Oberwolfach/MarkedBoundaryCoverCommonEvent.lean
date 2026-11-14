module

public import Oberwolfach.MarkedBoundaryExtensionRetention
public import Oberwolfach.MarkedCoverRetainedHost
public import Oberwolfach.TwoCommonEvents

@[expose] public section

/-! One boundary sample supplies the path extensions and compatible hubs.
No independence between these events is needed. The hub conclusion applies
to every later selected pair having the stated original common-neighbour
count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_boundary_cover_common_event (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀ (tail head:E→V) (ktail khead:K→V)
      (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U),
    (∀ j x u,β*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))→
    (∀ j x y u,x≠(if j then π y else y)→β*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ))→
    1-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>
          let P₀:=markedCoverRimAllowed π X σ false
          let P₁:=markedCoverRimAllowed π X σ true
          let E':={e:E//P₀ (tail e) (head e)}
          let K':={e:K//P₁ (ktail e) (khead e)}
          let t':=fun e:E'=>tail e.val
          let h':=fun e:E'=>head e.val
          let kt':=fun e:K'=>ktail e.val
          let kh':=fun e:K'=>khead e.val
          let H₀':=fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u
          let HK':=fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u;
          (∀ j x u,p^3*β*Fintype.card (V⊕U)/2≤((X.filter (fun z=>
            markedArcPresent t' h' kt' kh' j x z∧(if j then HK' z u else H₀' z u))).card:ℝ))∧
          (∀ j x y u,x≠(if j then π y else y)→p^3*β*Fintype.card (V⊕U)/2≤((X.filter (fun z=>
            markedArcPresent t' h' kt' kh' false x z∧markedArcPresent t' h' kt' kh' j z y∧H₀' z u)).card:ℝ))∧
          (∀ (j:Bool) x y,β*Fintype.card (V⊕U)≤(Z.filter (fun u=>H₀ x u∧(if j then HK y u else H₀ y u))).card→
            p^3*β*Fintype.card (V⊕U)/2≤(Z.filter (fun u=>H₀' x u∧(if j then HK' y u else H₀' y u))).card)):=by
  obtain ⟨N₁,hN₁⟩:=marked_boundary_extension_retention_event β p hβ hp hp1 q
  obtain ⟨N₂,hN₂⟩:=marked_boundary_hub_retention_event (p^3*β/2) (by positivity) q
  refine ⟨max N₁ N₂,?_⟩
  intro V U E K _ _ _ _ hn tail head ktail khead H₀ HK π X Z hstep hjoin
  have hpaths:=hN₁ V U E K (by omega) tail head ktail khead H₀ HK π X hstep hjoin
  have hhubs:=hN₂ V U (by omega) H₀ HK Z p hp.le hp1
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hpaths hhubs
  have hl:1-2/(Fintype.card (V⊕U):ℝ)^q=
      1-1/(Fintype.card (V⊕U):ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q:=by ring
  rw [hl]
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σ hσ P₀ P₁ E' K' t' h' kt' kh' H₀' HK'
  have hext:=marked_retained_cover_free_counts tail head ktail khead H₀ HK π X Z σ
    (p^3*β*Fintype.card (V⊕U)/2) hσ.1.1 hσ.1.2
  refine ⟨hext.1,hext.2,?_⟩
  intro j x y hxy
  have h:=hσ.2 j x y
  have hm:=mul_le_mul_of_nonneg_left hxy (pow_nonneg hp.le 3)
  apply marked_retained_cover_hub_counts H₀ HK X Z σ j x y
  nlinarith only [h,hm]
end Oberwolfach
