import BlancoSinPesoYVacanciasDelLleno
import MediaEspacialParaPruebasContinuas
import MediasFisicasDesdeUnCentroConvergente
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil Filter Set Limites
open scoped Topology
theorem psi_continua_en_el_cuadrado {p κ M L} (sp : ControlEspacial p κ M L) (lp : 0≤L) :
    ContinuousOn (fun z : ℝ×ℝ => psiDiagonal p z.1 z.2) cuadradoCerrado := by
  have d:=continua_de_cota lp sp.D.oscilacion
  have a:=continua_de_cota lp sp.A.oscilacion
  exact (d.comp (continuous_fst.sub continuous_snd).continuousOn
    (fun z hz => (dominios z.1 z.2 hz.1 hz.2).1)).mul
    (a.comp (continuous_fst.add continuous_snd).continuousOn (fun z hz => (dominios z.1 z.2 hz.1 hz.2).2))

theorem centro_inverso_sin_peso_tiende_a_Buno {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (j : ℕ) :
    Tendsto (fun n : ℕ => blancoInverso (n:=n) j (p ((j:ℝ)/n)) (fun _ => 1) 1/(n:ℝ)^2)
      atTop (𝓝 (integralTablero (psiDiagonal (p 0)))) := by
  have zero : (0:ℝ)∈Icc 0 (1/2:ℝ) := ⟨le_rfl,by norm_num⟩
  have s:=cuadratura_para_pruebas_continuas _ (psi_continua_en_el_cuadrado (rama.espacio 0 zero) rama.lp)
  have eq : Tendsto (fun n : ℕ => mediaExterior (fun z : Cell n => psiEnElCentro (p 0) z)) atTop
      (𝓝 (integralTablero (psiDiagonal (p 0)))) := s
  simpa only [sub_add_cancel,zero_add] using (centro_inverso_sin_peso_en_la_malla rama cont j).add eq

/-- Section 9(c): convergence in probability at level h-1 and the unweighted mean at level h. -/
theorem ley_del_conteo_sin_peso {P p b κ M L B} (rama : RamaDensa P p b κ M L B)
    (cont : ContinuidadEnElLleno p b) (first : CotaDePrimerOrden (valorCentrado (P 0))) (h : ℕ) (hh : 0<h) :
    (∀ ε>0,Tendsto (fun n => desviacion n (n-h+1) (Iobs n h (fun _ => 1))
      (integralTablero (psiDiagonal (p 0))) ε) atTop (𝓝 0)) ∧
    Tendsto (fun n => mediaD n h (fun _ => 1)) atTop (𝓝 (integralTablero (psiDiagonal (p 0))/b 0)) := by
  have center:=centro_inverso_sin_peso_tiende_a_Buno rama cont (h-1)
  let w:= fun (n : ℕ) (_ : Cell n) => (1:ℝ)
  have cap (n) (z : Cell n) : |w n z|≤1 := by simp [w]
  refine ⟨(inversa_con_centro_convergente rama first h hh w zero_le_one cap center).1,?_⟩
  have direct:=media_directa_con_centro_convergente rama cont first h hh w zero_le_one cap center
  have eq : fraccionDelPerfil b 0*integralTablero (psiDiagonal (p 0))=integralTablero (psiDiagonal (p 0))/b 0 := by
    unfold fraccionDelPerfil; simp; ring
  rw [eq] at direct
  exact direct
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.psi_continua_en_el_cuadrado
#print axioms ArticuloA.Historias.centro_inverso_sin_peso_tiende_a_Buno
#print axioms ArticuloA.Historias.ley_del_conteo_sin_peso
