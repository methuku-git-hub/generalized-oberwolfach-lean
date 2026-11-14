module

public import Oberwolfach.DirectedBoundaryRobustSupportEvent
public import Oberwolfach.MarkedBoundarySupportEvent
public import Oberwolfach.MarkedBoundaryPhysicalCoordinates

@[expose] public section

/-! The actual marked boundary support event under the original physical
Bernoulli law, including successor labels and all outside rows and hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_boundary_robust_support_event (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K],
    N≤Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
      (X:Finset V) (Z:Finset U),
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ τ:Sym2 (V⊕U)→Bool,
            (∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge
              (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)=>
              (markedActiveAuxTail tail ktail H₀ HK a.val=x∨markedActiveAuxHead head khead H₀ HK a.val=x)∧
              σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
                τ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val))).card:ℝ)≤p^2*Fintype.card (V⊕U)/2)→
            (∀ x,((markedBoundarySupport tail head ktail khead π H₀ HK X Z τ x).card:ℝ)≤14*p*Fintype.card (V⊕U))∧
            (∀ x y,x≠y→((markedBoundarySupport tail head ktail khead π H₀ HK X Z τ x∩
              markedBoundarySupport tail head ktail khead π H₀ HK X Z τ y).card:ℝ)≤(14*p)^2*Fintype.card (V⊕U))∧
            (∀ v,((Finset.univ.filter (fun x=>v∈markedBoundarySupport tail head ktail khead π H₀ HK X Z τ x)).card:ℝ)≤
              14*p*Fintype.card (V⊕U))) := by
  obtain ⟨N,hN⟩:=directed_boundary_robust_support_event p hp hp1 q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ _ _ hn tail head ktail khead π H₀ HK X Z hphys
  let coin:MarkedActiveEdge E K H₀ HK↪Sym2 (V⊕U):=
    ⟨markedActivePhysicalCoin tail head ktail khead π H₀ HK,
      markedActivePhysicalCoin_injective tail head ktail khead π H₀ HK hphys⟩
  exact hN (MarkedActiveEdge E K H₀ HK) (V⊕U) (Sym2 (V⊕U)) (Fin 3) hn (by simp)
    (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK)
    (markedActiveDirectionTag H₀ HK) coin (ordinaryInnerVertices X Z) (Equiv.sumCongr π (Equiv.refl U))
    (markedActive_typed_endpoints_injective tail head ktail khead π H₀ HK hphys)

end Oberwolfach
