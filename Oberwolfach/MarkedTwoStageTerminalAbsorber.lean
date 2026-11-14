module

public import Oberwolfach.MarkedTwoStageTerminalDeletionGraphs
public import Oberwolfach.MarkedReservedFirstDeletionProtection
public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.MarkedReservedAbsorberAdaptiveDeletion

@[expose] public section
/-! If the final pair lies in the active pair, a preselected absorber
continues to absorb every divisible terminal remainder after both packings. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
def MarkedTerminalAbsorberForGraphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ₀:RawMarkedOutcome V U Γ Color) (H₀:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)):Prop:=
      let σ:=rawMarkedDeleteRims σ₀ DR.edgeFinset
      let H:=markedDeletePhysicalSpokes H₀ DS
      let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
      let tail:=fun e:E=>e.val.1
      let head:=fun e:E=>e.val.2
      let ktail:=fun e:K=>e.val.1
      let khead:=fun e:K=>e.val.2;
      ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
      (∀ a∈A,Sum.elim tail ktail a∈Xterm∧Sum.elim head khead a∈Xterm)→
      (∀ z∈S,z.1∈Xterm∧z.2∈Zterm∧(H false z.1 z.2∨H true z.1 z.2))→
      MarkedRemainderDivisible tail head ktail khead (H true) A S m→
      IsResourceAbsorber
        (fun Q:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources Q)
        (markedFiniteResources tail head ktail khead π A S) C


def MarkedUniversalTerminalDeletionAbsorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ₀:RawMarkedOutcome V U Γ Color) (H₀:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U):Prop:=
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y)→
      (∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u))→
      (∀ v∈Xterm,∀ u∈Zterm,¬DS.Adj (Sum.inl v) (Sum.inr u))→
      MarkedTerminalAbsorberForGraphs P π d m σ₀ H₀ C Xterm Zterm DR DS

theorem marked_two_stage_preserves_terminal_absorption
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ₀:RawMarkedOutcome V U Γ Color) (H₀:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hpriorR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬FR.Adj x y)
    (hpriorS:∀ v u,Sum.inr (v,u)∈C→¬FS.Adj (Sum.inl v) (Sum.inr u))
    (hpriorTerm:∀ v∈Xterm,∀ u∈Zterm,¬FS.Adj (Sum.inl v) (Sum.inr u))
    (habs:MarkedUniversalTerminalDeletionAbsorber P π d m σ₀ H₀ C Xterm Zterm)
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I)
    (hX:Xterm⊆I\T) (hZ:Zterm⊆J\W) (hC:∀ e∈C,¬markedInnerResource I J e):
    let σ:=rawMarkedDeleteRims σ₀ FR.edgeFinset
    let H:=markedDeletePhysicalSpokes H₀ FS
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A₀:Finset (E⊕K)) (S₀:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (R:Finset (Finset V⊕(V×U))),
    (∀ a∈A₀,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S₀,z.1∈I∧z.2∈J)→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=R.filter (markedStarResource T W)→
    let Astar:=A₀.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let Sstar:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let DR₁:=markedSampleArcSetGraph P π d σ (Astar∪M.biUnion markedWheelArcs)
    let DS₁:=markedFiniteSpokeGraph (Sstar∪M.biUnion markedWheelSpokePairs)
    let σ₁:=rawMarkedDeleteRims σ DR₁.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS₁
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) false
    let K₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) true;
    ∀ N:Finset (MarkedWheel (fun e:E₁=>e.val.1) (fun e=>e.val.2)
      (fun e:K₁=>e.val.1) (fun e=>e.val.2) m π (3*d) (H₁ false) (H₁ true)),
    Disjoint C (N.biUnion markedWheelPhysicalResources)→
    (N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    let DR₂:=markedPackingRimGraph N
    let DS₂:=markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs)
    let DR:=FR⊔(DR₁⊔DR₂)
    let DS:=FS⊔(DS₁⊔DS₂)
    MarkedTerminalAbsorberForGraphs P π d m σ₀ H₀ C Xterm Zterm DR DS :=by
  intro σ H E K tail head ktail khead A₀ S₀ M R hA₀ hS₀ hMC hM Astar Sstar DR₁ DS₁ σ₁ H₁ E₁ K₁ N hNC hN DR₂ DS₂ DR DS
  have hg:=marked_two_stage_terminal_deletion_graphs P π d m σ₀ H₀ C Xterm Zterm FR FS hpriorR hpriorS hpriorTerm
    I T J W hI hX hZ hC A₀ S₀ M R hA₀ hS₀ hMC hM N hNC hN
  exact habs DR DS hg.1 hg.2.1 hg.2.2
end Oberwolfach
