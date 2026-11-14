import UsoDeUnaLineaEnLaEsperanzaDetenida
import SumaDeLosUsosDeLineaSinDuplicarFibras
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def usoDeFibraEnEstado {n} (v : Cell n→ℝ≥0) (q t : ℕ) (j : FibraDeB1 n) : EstadoGuiado n→ℝ
  | none=>0
  | some l=>masaBajo (leyDePieza v q t l) (enLaFibra j)

theorem uso_de_la_fibra_etiquetada {n} (v : Cell n→ℝ≥0) (q t : ℕ) (i : Fin 4) (z : Cell n) (s : EstadoGuiado n) :
    usoDeFibraEnEstado v q t (etiquetaDeCasilla z i) s=usoDeLineaEnEstado v q t i z s := by
  cases s with
  | none=>rfl
  | some l=>
    unfold usoDeFibraEnEstado usoDeLineaEnEstado masaBajo riesgoDeLinea
    apply Finset.sum_congr rfl
    intro e _
    by_cases yes : llaveDeLinea i e=llaveDeLinea i z
    · simp only [pesoCuando,if_pos yes,if_pos ((llave_de_la_fibra_en_G i z e).mp yes)]
    · simp only [pesoCuando,if_neg yes,if_neg (mt (llave_de_la_fibra_en_G i z e).mpr yes)]

theorem cota_de_uso_para_toda_etiqueta {n q t : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t≤q)
    (j : FibraDeB1 n) {η E : ℝ} (hp : 0<η) (h1 : η≤1) (en : 0≤E) (es : E≤1/10)
    (sm : 1/(η*q)≤1/2) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η)
    (keep : List (EstadoGuiado n)→Prop) (ok : ∀ hist,keep hist→
      prefijoRegular (guardaDelErrorFisico v q E) 0 (some []) hist ∧
        guardaDelErrorFisico v q E t (ultimoEstado (some []) hist)) :
    let H:=E/((9/10)*η*q)
    let m:=masaBajo (fun e=>(v e:ℝ)) (enLaFibra j)
    media (rutas (pasoDeG v q) 0 t (some [])) (fun hist=>if keep hist then
      usoDeFibraEnEstado v q t j (ultimoEstado (some []) hist) else 0)≤
        exp (2*H*q)*(m/q+H*(1-(t:ℝ)/q*m)) := by
  classical
  intro H m
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have hn : 0≤H:=by dsimp [H]; positivity
  by_cases hit : ∃ (e : Cell n) (i : Fin 4),etiquetaDeCasilla e i=j
  · obtain ⟨e,i,rfl⟩:=hit
    have mass:=masa_de_linea_en_G_es_la_de_B1 v i e
    have frac:=margen_de_fraccion_viva qp tq v slack h1 e i
    have fact : 0≤(masaDeLineaG v i e:ℝ)/q+H*fraccionVivaG v q t e i:=
      add_nonneg (div_nonneg (NNReal.coe_nonneg _) qr.le) (mul_nonneg hn (hp.le.trans frac))
    have ex:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (show (t:ℝ)≤q by exact_mod_cast tq) (by positivity : 0≤2*H))
    have bound:=esperanza_de_uso_de_linea_en_prefijos v qp tq i e hp h1 en es sm slack keep ok
    simp_rw [uso_de_la_fibra_etiquetada]
    dsimp only [m]
    rw [←mass]
    exact bound.trans (mul_le_mul_of_nonneg_right ex fact)
  · have empty (e : Cell n) : ¬enLaFibra j e:=by
      intro belongs
      have eq : etiquetaDeCasilla e (familiaDeReserva j)=j:=by
        rcases j with ⟨c,s⟩|⟨c,s⟩ <;> cases c <;> simpa [familiaDeReserva,enLaFibra,etiquetaDeCasilla,etiquetaD,etiquetaA] using belongs
      exact hit ⟨e,_,eq⟩
    have no (p : Cell n→ℝ) : masaBajo p (enLaFibra j)=0:=by simp [masaBajo,pesoCuando,empty]
    have zero (s : EstadoGuiado n) : usoDeFibraEnEstado v q t j s=0:=by cases s <;> simp [usoDeFibraEnEstado,no]
    simp only [m,no,zero,ite_self,zero_div,mul_zero,sub_zero,mul_one,zero_add]
    have z:=media_affine (rutas (pasoDeG v q) 0 t (some [])) (fun _=>0) 0 0
    simp only [mul_zero,add_zero,zero_add,zero_mul] at z
    rw [z]
    positivity
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_de_uso_para_toda_etiqueta
