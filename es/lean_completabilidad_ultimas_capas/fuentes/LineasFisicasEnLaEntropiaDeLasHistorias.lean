import UsoFisicoPorEtiquetaIncluidasLasFibrasVacias
import PresupuestoSumadoDeLasFibrasFisicas
import MediaDeUnaSumaDeMarcas
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def aporteFisicoDeLineas {n} (v : Cell n→ℝ≥0) (q t : ℕ) : EstadoGuiado n→ℝ
  | none=>0
  | some l=>∑ e,leyDePieza v q t l e*∑ i,log (fraccionVivaG v q t e i)

theorem aporte_reunido_por_lineas {n} (v : Cell n→ℝ≥0) (q t : ℕ) (s : EstadoGuiado n) :
    aporteFisicoDeLineas v q t s=∑ j,usoDeFibraEnEstado v q t j s*
      log (1-(t:ℝ)/q*masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)) := by
  cases s with
  | none=>simp [aporteFisicoDeLineas,usoDeFibraEnEstado]
  | some l=>
    simp only [aporteFisicoDeLineas,usoDeFibraEnEstado]
    rw [←suma_de_las_cargas_por_incidencia (leyDePieza v q t l) (fun j=>log (1-(t:ℝ)/q*masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)))]
    simp_rw [fraccionVivaG,masa_de_linea_en_G_es_la_de_B1]

theorem holgura_para_cada_etiqueta {n} (v : Cell n→ℝ≥0) {η : ℝ} (h1 : η≤1)
    (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) (j : FibraDeB1 n) :
    masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)≤1-η := by
  by_cases hit : ∃ (e : Cell n) (i : Fin 4),etiquetaDeCasilla e i=j
  · obtain ⟨e,i,rfl⟩:=hit
    rw [←masa_de_linea_en_G_es_la_de_B1]
    exact slack i e
  · have empty (e : Cell n) : ¬enLaFibra j e:=by
      intro belongs
      have eq : etiquetaDeCasilla e (familiaDeReserva j)=j:=by
        rcases j with ⟨c,s⟩|⟨c,s⟩ <;> cases c <;> simpa [familiaDeReserva,enLaFibra,etiquetaDeCasilla,etiquetaD,etiquetaA] using belongs
      exact hit ⟨e,_,eq⟩
    simpa [masaBajo,pesoCuando,empty] using sub_nonneg.mpr h1

theorem aporte_esperado_de_las_cuatro_familias {n q : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q)
    (mass : ∑ e,(v e:ℝ)=q) {η E : ℝ} (hp : 0<η) (h1 : η≤1) (en : 0≤E) (es : E≤1/10)
    (sm : 1/(η*q)≤1/2) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    (keep : ℕ→List (EstadoGuiado n)→Prop) (ok : ∀ t<q,∀ hist,keep t hist→
      prefijoRegular (guardaDelErrorFisico v q E) 0 (some []) hist ∧
        guardaDelErrorFisico v q E t (ultimoEstado (some []) hist)) :
    let H:=E/((9/10)*η*q)
    let b:=exp (2*H*q)
    entropiaLineas (fun e=>(v e:ℝ))-4*q-4*q*((b-1)+b*H*q)/η≤
      ∑ t∈Finset.range q,media (rutas (pasoDeG v q) 0 t (some [])) (fun hist=>if keep t hist then
        aporteFisicoDeLineas v q t (ultimoEstado (some []) hist) else 0) := by
  classical
  intro H b
  let law t:=rutas (pasoDeG v q) 0 t (some [])
  let val t j (hist : List (EstadoGuiado n)):=if keep t hist then usoDeFibraEnEstado v q t j (ultimoEstado (some []) hist) else 0
  let f (t : ℕ) (j : FibraDeB1 n):=log (1-(t:ℝ)/q*masaBajo (fun e=>(v e:ℝ)) (enLaFibra j))
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have hn : 0≤H:=by dsimp [H]; positivity
  have b1 : 1≤b:=Real.one_le_exp (by positivity)
  apply (lineas_integradas_con_error_total qp v mass (fun t j=>media (law t) (val t j)) hp hn b1
    (holgura_para_cada_etiqueta v h1 slack) (fun j t ht=>cota_de_uso_para_toda_etiqueta v qp ht.le j hp h1 en es sm slack (keep t) (ok t ht))).trans_eq
  apply Finset.sum_congr rfl
  intro t _
  have integrate j : media (law t) (fun h=>val t j h*f t j)=media (law t) (val t j)*f t j:=by
    have eq:=media_affine (law t) (val t j) 0 (f t j)
    simpa only [zero_add,mul_zero,mul_comm (f t j)] using eq
  have point (h : List (EstadoGuiado n)) :
      (∑ j,val t j h*f t j)=(if keep t h then aporteFisicoDeLineas v q t (ultimoEstado (some []) h) else 0):=by
    by_cases yes : keep t h <;> simp only [val,f,yes,if_true,if_false,zero_mul,Finset.sum_const_zero,aporte_reunido_por_lineas]
  change (∑ j,media (law t) (val t j)*f t j)=_
  simp_rw [←integrate]
  rw [←media_de_suma_finita]
  simp_rw [point]
  rfl
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.aporte_esperado_de_las_cuatro_familias
