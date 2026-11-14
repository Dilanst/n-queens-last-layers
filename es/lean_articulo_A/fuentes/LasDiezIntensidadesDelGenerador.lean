import ImpactosDeFuentesYDestinos
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

private theorem tasa_activa {n} (X : State n) (w : ColorWeights ℝ≥0) (u : Vertex)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0) :
    meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (consumeVertex a u.1 u.2))=
      tasaDeMarca X w u true := by
  have eq (a : Choice n) : indicator (consumeVertex a u.1 u.2)=
      indicator (colourAt true u a=true)+indicator (colourAt false u a=true) := by
    cases a <;> simp [consumeVertex,colourAt,hitsVertex,indicator]
  rw [funext eq,mean_plus,real_rate masas X w (·⁻¹) rr vv,virtual_rate masas X w (·⁻¹) rr vv]
  rfl

private theorem intensidad_fuente {n} (X : State n) (w : ColorWeights ℝ≥0) (u : Vertex) (U : Prop)
    (k : Bool) (hit : Choice n→Prop) (same : ∀ a,hit a ↔ consumeVertex a u.1 u.2 ∧ k=false)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0) :
    meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (U ∧ hit a))=
      if U ∧ k=false then tasaDeMarca X w u true else 0 := by
  by_cases live : U ∧ k=false
  · rw [if_pos live,←tasa_activa X w u rr vv]
    apply mean_eq; intro a _
    exact congrArg indicator (propext (by rw [same]; tauto))
  · rw [if_neg live]
    apply Eq.trans _ (mean_zero masas (choices masas X w (·⁻¹)))
    apply mean_eq; intro a _
    exact if_neg (fun yes => live ⟨yes.1,((same a.2).mp yes.2).2⟩)

def bajasFuente {n} (X : State n) (w : ColorWeights ℝ≥0) (e : Cell n) (U : Prop) (o : Bool) : ℝ≥0 :=
  ∑ i : Fin 4,if U ∧ o=false then tasaDeMarca X w (lineLabel e i) true else 0

def bajasDestino {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (o v j l : Bool) : ℝ≥0 :=
  (if patronInverso X e f o v true l then tasaDeMarca X w (lineLabel (corners (e,f)).2 2) j else 0)+
  (if patronInverso X e f o v j true then tasaDeMarca X w (lineLabel (corners (e,f)).2 3) l else 0)

theorem descomponer_intensidades {n} (X : State n) (w : ColorWeights ℝ≥0) (e f : Cell n)
    (o v j l : Bool) (ok : compatible e f) (coh : coherent X)
    (rr : total masas (realChoices masas X w)≠0) (vv : total masas (virtualChoices masas X w)≠0) :
    let U:=patronInverso X e f o v j l
    let H:=fun u => meanN masas (choices masas X w (·⁻¹))
      (fun a => indicator (U ∧ golpeDelPar e f o v j l a u))
    masas.sum (diez e f) H=bajasFuente X w e U o+bajasFuente X w f U v+bajasDestino X w e f o v j l := by
  intro U H
  have se (i : Fin 4) := intensidad_fuente X w (lineLabel e i) U o _
    (fun a => (impactos_sobre_las_fuentes e f ok i o v j l a).1) rr vv
  have sf (i : Fin 4) := intensidad_fuente X w (lineLabel f i) U v _
    (fun a => (impactos_sobre_las_fuentes e f ok i o v j l a).2) rr vv
  obtain ⟨de,df⟩:=dos_tasas_del_destino X w e f o v j l coh rr vv
  have target (i : Fin 4) (b : Bool) (eq : ∀ a,golpeDelPar e f o v j l a (lineLabel (corners (e,f)).2 i) ↔
      borraMarca e f i b a) : H (lineLabel (corners (e,f)).2 i)=
      meanN masas (choices masas X w (·⁻¹)) (fun a => indicator (U ∧ borraMarca e f i b a)) := by
    apply mean_eq; intro a _; exact congrArg indicator (propext (and_congr_right fun _ => eq a.2))
  have t2:=(target 2 j (fun a => (impactos_sobre_los_destinos e f ok o v j l a).1)).trans de
  have t3:=(target 3 l (fun a => (impactos_sobre_los_destinos e f ok o v j l a).2)).trans df
  change ∀ i,H (lineLabel e i)=_ at se
  change ∀ i,H (lineLabel f i)=_ at sf
  change H (lineLabel e 0)+(H (lineLabel e 1)+(H (lineLabel e 2)+(H (lineLabel e 3)+
    (H (lineLabel f 0)+(H (lineLabel f 1)+(H (lineLabel f 2)+(H (lineLabel f 3)+
    (H (lineLabel (corners (e,f)).2 2)+(H (lineLabel (corners (e,f)).2 3)+0)))))))))=_
  simp only [t2,t3,se,sf,bajasFuente,bajasDestino,Fin.sum_univ_four,add_zero]
  ac_rfl

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.descomponer_intensidades
