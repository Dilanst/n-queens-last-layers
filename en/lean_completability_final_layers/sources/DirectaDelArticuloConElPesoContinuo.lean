import IdentificacionUniformeEnElTableroLleno
import DirectaPonderadaEnLaMalla
import ConteoDePrimerOrdenSinVecindades
open Set Filter
open scoped Topology
namespace ArticuloA.Historias
open Perfil Limites Repair
noncomputable section
open Classical

private theorem comparar_eventos {n h} (a b : Cell n→ℝ) (ε : ℝ) (close : ∀ z,|a z-b z|≤ε/2) :
    probCruceMalo n h b ε≤probCruceMalo n h a (ε/2) := by
  apply Finset.sum_le_sum; intro p _
  by_cases bad : ∃ z∈cruces p,ε< |(crossDegree (n-h) p z:ℝ)/n-b z|
  · obtain ⟨z,hz,high⟩:=bad
    have tri:=abs_sub_le ((crossDegree (n-h) p z:ℝ)/n) (a z) (b z)
    have old : ∃ z∈cruces p,ε/2< |(crossDegree (n-h) p z:ℝ)/n-a z| :=
      ⟨z,hz,by linarith [close z]⟩
    rw [if_pos ⟨z,hz,high⟩,if_pos old]
  · rw [if_neg bad]; split <;> positivity

/-- Section 9, direct law on the actual centered full-profile target and two forms of
weighted convergence. The first-order counting theorem and the endpoint data are inputs. -/
theorem directa_del_articulo {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (pt : EulerPuntualDeRama p b) (cont : ContinuidadEnElLleno p b)
    (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h) :
    let a:=fun (n : ℕ) => aDelLleno (n:=n) p b
    let w:=fun n z => 1/a n z
    (∀ η>0,Tendsto (fun n => probCruceMalo n h (a n) η) atTop (𝓝 0)) ∧
    (∀ ε>0,Tendsto (fun n => desviacion n (n-h) (Dobs n h (w n)) 1 ε) atTop (𝓝 0)) ∧
    Tendsto (fun n => mediaD n h (w n)) atTop (𝓝 1) := by
  intro a w
  have ext := (conteo_equivalente_al_primer_orden _).mpr first
  obtain ⟨C,bal⟩:=balance_de_la_rama_puntual rama pt
  have mesh := directa_de_la_rama rama h (fun _ => ext) (fun _ => h) (Eventually.of_forall (fun _ => le_rfl)) C (bal h)
  have same:=malla_converge_al_lleno rama pt cont h
  have direct (η : ℝ) (ep : 0<η) :
      Tendsto (fun n => probCruceMalo n h (a n) η) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (mesh (η/2) (half_pos ep))
    · apply Eventually.of_forall; intro n; unfold probCruceMalo
      apply Finset.sum_nonneg; intro _ _; split <;> positivity
    · filter_upwards [same (η/2) (half_pos ep)] with n hn
      exact comparar_eventos _ _ _ hn
  refine ⟨direct,?_⟩
  let m := (κ/2)^4/4
  have pos : 0<(κ/2)^4 := pow_pos (half_pos rama.kp) 4
  have mp : 0<m := by dsimp [m]; positivity
  have floor:=piso_eventual_de_las_raices rama h C (bal h) ((κ/2)^4/2) (half_lt_self pos)
  have lower : ∀ᶠ n : ℕ in atTop,∀ z,m≤a n z := by
    filter_upwards [floor,same m mp] with n hf hc
    intro z
    have low : (κ/2)^4/2≤blancoNormalizado h (p ((h:ℝ)/n)) z := hf z
    have clos : blancoNormalizado h (p ((h:ℝ)/n)) z-a n z≤m := (abs_le.mp (hc z)).2
    dsimp [m] at clos ⊢; linarith only [low,clos]
  have valid : ∀ᶠ n : ℕ in atTop,0<count n (n-h) := by
    filter_upwards [soluciones_eventuales_del_primer_orden first,eventually_ge_atTop h] with n hn nh
    exact capa_positiva_si_hay_solucion nh hn
  exact directa_ponderada_desde_cruces h hh a m mp valid lower direct
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.directa_del_articulo
