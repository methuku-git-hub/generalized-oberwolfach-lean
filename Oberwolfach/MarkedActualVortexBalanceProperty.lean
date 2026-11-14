module

public import Oberwolfach.MarkedActualInnerBalanceEvent

@[expose] public section
/-! A name for the explicit, fixed-domain balance event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def MarkedActualVortexBalanceProperty
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U] {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d c L:ℕ) (a:Γ) (j:Color) (epsBal ζ:ℝ)
    (A:∀ i,Finset (markedVortexVertexType Q i))
    (B:∀ i,Finset (markedVortexHubType Q i))
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a):Prop :=
  let W:=markedVortexVertexType Q
  letI : ∀ i,DecidableEq (W i):=fun _ x y=>Classical.propDecidable (x=y)
  let Z:=markedVortexHubType Q
  let f:=markedVortexVertexEmbedding Q
  let g:=markedVortexHubEmbedding Q
  let ρ:=markedVortexPermutation Q π hπ
  let M:=fun i=>(A i).card
  ∀ i≤L,
          let σi := rawMarkedRestrictPair (f i) (g i) z.1
          let Hi := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
          let E := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) false
          let KArc := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σi (Sum.inl e)) true
          let S := Finset.univ.filter (fun s:W i×Z i=>Hi false s.1 s.2∨Hi true s.1 s.2)
          let err := (epsBal+(c+2:ℕ)*ζ)*M i;
          (∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j|≤err) ∧
          ∀ (KA : Finset (E⊕KArc)) (KS : Finset (W i×Z i)),KS⊆S→
          let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) KA KS;
          R.filter (markedInnerResource (A i) (B i))=∅→
          ∀ δ:ℝ,0≤δ→
          (∀ physical v,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) (Hi false) (Hi true) physical v).filter
            (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρ i) (Hi false) (Hi true) e∈
                R.filter (markedStarResource (A i) (B i)))).card:ℝ)≤δ)→
          let σ' := rawMarkedDeleteRims σi (markedSampleArcSetGraph (G.comap (f i)) (ρ i) d σi KA).edgeFinset
          let H' := markedDeletePhysicalSpokes Hi (markedFiniteSpokeGraph KS)
          let E' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) false
          let K' := MarkedSampleArc (G.comap (f i)) (ρ i) (3*d) (fun e=>σ' (Sum.inl e)) true
          let S' := Finset.univ.filter (fun s:W i×Z i=>H' false s.1 s.2∨H' true s.1 s.2);
          (∀ v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
            (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j|≤err+(c+2)*δ) ∧
          (∀ v,Sum.elim (fun x=>x∈A i) (fun u=>u∈B i) v→∀ j,
            markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
              (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' c (A i) (B i) v j=
            markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S c (A i) (B i) v j) 
end Oberwolfach
