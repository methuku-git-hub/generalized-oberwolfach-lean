module

public import Oberwolfach.MarkedParentLoadRecordInputs
public import Oberwolfach.MarkedActualParentPackingEvent

@[expose] public section
/-! Original-sample parent load fields on the actual fixed vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_parent_load_record_inputs
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (p k s₀ η C κ thetaDeep:ℝ)
    (hpot:η≤κ/4) (hlocal:η≤thetaDeep/4)
    (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (weight:∀ i,(Fin (c+1)→markedVortexVertexType Q i)→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hadapt:∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (markedVortexVertexType Q i))
      (DS:SimpleGraph (markedVortexVertexType Q i⊕markedVortexHubType Q i)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hπ i) d c
        (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D) p k s₀ (weight i) a j
        (Function.Embedding.refl (markedVortexHubType Q i)) (fun u=>q (markedVortexHubEmbedding Q i u))
        (fun u=>s (markedVortexHubEmbedding Q i u)) (η+C*δ/Fintype.card (markedVortexVertexType Q i))
        (rawMarkedDeleteRims (rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1) DR.edgeFinset)
        (markedDeletePhysicalSpokes (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
          (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)) DS)):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let P:=G.comap (markedVortexVertexEmbedding Q i)
      let ρ:=markedVortexPermutation Q π hπ i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q i u)
      let si:=fun u=>s (markedVortexHubEmbedding Q i u);
      MarkedLocalSpokeLoadsWithSpokes P ρ d c Dload p k s₀ (weight i) (thetaDeep/4) σ H ∧
      (let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd c ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weight i X.1.val/(Dload*p^c*k*s₀^c);
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p k qi si a j root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4):=by
  intro i hi W Z P ρ Dload σ H qi si
  have hh:=marked_parent_load_record_inputs P ρ d c Dload p k s₀ (weight i) a j qi si η C κ thetaDeep
    hpot hlocal σ H (hadapt i hi)
  have heq:(fun x y:W=>Classical.propDecidable (x=y))=(fun x y:W=>Subtype.instDecidableEq x y):=Subsingleton.elim _ _
  rw [heq] at hh
  exact hh
end Oberwolfach
