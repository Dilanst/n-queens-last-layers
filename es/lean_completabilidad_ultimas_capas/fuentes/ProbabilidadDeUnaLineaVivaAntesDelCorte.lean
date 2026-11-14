import SupervivenciaDeUnaLineaConPrefijosRegulares
import RazonDeSupervivenciaDeLaLineaFisica
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def guardaDelErrorFisico {n} (v : Cell n→ℝ≥0) (q : ℕ) (E : ℝ) (t : ℕ) : EstadoGuiado n→Prop
  | none=>False
  | some l=>sigueTableroYLineas v q t l E

theorem masa_de_linea_viva_y_padres_regulares {n q m : ℕ} (v : Cell n→ℝ≥0) (qp : 0<q) (mq : m≤q)
    (i : Fin 4) (z : Cell n) {η E : ℝ} (hp : 0<η) (h1 : η≤1) (en : 0≤E) (es : E≤1/10)
    (small : 1/(η*q)≤1/2) (slack : ∀ j e,(masaDeLineaG v j e:ℝ)≤1-η) :
    let H:=E/((9/10)*η*q)
    let G:=guardaDelErrorFisico v q E
    (avg masas (rutas (pasoDeG v q) 0 m (some [])) (mark masas (caminoVivo G (lineaVivaEnEstado i z) 0 (some [])))).val≤
      fraccionVivaG v q m z i*exp (2*H*m) := by
  let H:=E/((9/10)*η*q)
  let lineFrac (s : ℕ):=fraccionVivaG v q s z i
  let b (s : ℕ):=Real.toNNReal ((lineFrac (s+1)/lineFrac s)*exp (2*H))
  let G:=guardaDelErrorFisico v q E
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have hn : 0≤H:=by dsimp [H]; positivity
  have pos s (sq : s≤q) : 0<lineFrac s:=hp.trans_le (margen_de_fraccion_viva qp sq v slack h1 z i)
  have br s (sq : s<q) : (b s:ℝ)=(lineFrac (s+1)/lineFrac s)*exp (2*H):=
    Real.coe_toNNReal _ (mul_nonneg (div_nonneg (pos _ (Nat.succ_le_of_lt sq)).le (pos _ sq.le).le) (exp_pos _).le)
  have rate s (_ : 0≤s) (st : s<0+m) (y : EstadoGuiado n) (g : G s y) (live : lineaVivaEnEstado i z y) :
      avg masas (pasoDeG v q s y) (mark masas (lineaVivaEnEstado i z))≤b s:=by
    have sq : s<q:=by omega
    cases y with
    | none=>exact False.elim g
    | some l=>
      have safe:=regularidad_del_padre_fisico v qp sq l hp.le es slack g
      have low:=safe.2.1
      have reg : total masas (opcionesGuiadas v q s l)≠0:=by
        intro no; rw [no] at low; change (9/10:ℝ)*q≤0 at low; linarith
      have root:=g.2 i z live
      rw [add_comm] at root
      have raw:=cota_temporal_del_error_de_riesgo v qp sq.le l reg i z hp h1 slack low root
      have err : |riesgoDeLinea (leyDePieza v q s l) z i-riesgoPrevisto v q s z i|≤H:=by
        apply raw.trans
        apply div_le_div_of_nonneg_left en (by positivity)
        have a:=mul_le_mul_of_nonneg_left (show (s:ℝ)≤q by exact_mod_cast sq.le) (sub_nonneg.mpr h1)
        linarith only [a]
      have ref : riesgoPrevisto v q s z i≤1/(η*q):=by
        apply div_le_div₀ zero_le_one ((slack i z).trans (by linarith)) (mul_pos hp qr)
        rw [mul_comm η]; exact mul_le_mul_of_nonneg_left (margen_de_fraccion_viva qp sq.le v slack h1 z i) qr.le
      apply NNReal.coe_le_coe.mp
      have step:=factor_de_supervivencia_con_error (ref.trans small) hn err
      rw [razon_entre_holguras_consecutivas v qp z i (pos s sq.le)] at step
      exact (masa_fisica_de_supervivencia_en_un_paso v l reg i z live).le.trans (step.trans_eq (br s sq).symm)
  have path:=producto_de_supervivencia_con_parada (pasoDeG v q) G (lineaVivaEnEstado i z) b 0 m (some []) rate
  have init : mark masas (lineaVivaEnEstado i z) (some ([] : List (Cell n)))=1:=by simp [mark,lineaVivaEnEstado,masas]
  rw [init,one_mul] at path
  have product t (tq : t≤q) : (∏ s∈Finset.range t,(b s:ℝ))=lineFrac t*exp (2*H*t):=by
    induction t with
    | zero=>simp [lineFrac,fraccionVivaG]
    | succ t ih=>
      rw [Finset.prod_range_succ,ih (by omega),br t (by omega),Nat.cast_succ,mul_add,mul_one,Real.exp_add]
      field_simp [(pos t (by omega)).ne']; ring
  change _≤lineFrac m*exp (2*H*m)
  apply (NNReal.coe_le_coe.mpr path).trans
  simpa only [NNReal.coe_prod,Nat.zero_add] using (product m mq).le
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_de_linea_viva_y_padres_regulares
