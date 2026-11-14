module

public import Oberwolfach.MarkedFixedVortexReferenceActiveAbsorberEvent

@[expose] public section
/-! The reference, active-neighbourhood and robust-absorber event on a
single retained outcome, with the manuscript's fixed vortex and profiles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

def MarkedReferenceActiveAbsorberProperty
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a):Prop:=
  let W:=markedVortexVertexType Q
  let Z:=markedVortexHubType Q
  let f:=markedVortexVertexEmbedding Q
  let g:=markedVortexHubEmbedding Q
  let ρ:=markedVortexPermutation Q π hpres
  let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
  let I:=markedVortexInnerVertices Q
  let T:=markedVortexDeeperVertices Q
  let J:=markedVortexInnerHubs Q
  let Wrem:=markedVortexDeeperHubs Q;
  (fun z=>((∀ i≤L,
        MarkedReferenceConfigurations r (G.comap (f i)) (ρ i) d a j βconfig
          (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ→2*ζ≤(3/4)*(α/2)*p^2→ζ≤(α/2)*min p k/8→
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i))→
        MarkedReferenceStatistics (G.comap (f i)) (ρ i) d a j (Dload i) (εref+ζ) δref ((α/2)/2) p k s₀ (s₀/((r+4:ℕ):ℝ))
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (G.comap (f i)) (ρ i) d a j ((α/2)/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset)) ∧ (∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩(I i\T i)).card:ℝ)≤deltaR)→
            (∀ x,((((J i\Wrem i)).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,((((I i\T i)).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (G.comap (f i)) (ρ i) d h ((I i\T i)) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζActive)*((I i\T i)).card+h*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρ i) d h ((J i\Wrem i))
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((tol+h*ζActive)*((J i\Wrem i)).card+h*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS))) ∧ (let Habs:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
          ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
            (∀ x,(DR.degree x:ℝ)≤ζAbs*Fintype.card V)→
            (∀ x,(DS.degree x:ℝ)≤ζAbs*Fintype.card V)→
          let σ':=rawMarkedDeleteRims z.1 DR.edgeFinset
          let H':=markedDeletePhysicalSpokes Habs DS
          MarkedReservedTerminalAbsorberProperty
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs)) z
end Oberwolfach
