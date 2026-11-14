import SeguimientoHastaUnaRaizVivaDelCaminoFisico
import DerivasFisicasEnElEventoDeSeguimiento
import ValoresFisicosEnElOrigenDelProcesoGuiado
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

abbrev tableroG {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) : ℝ :=
  (total masas (opcionesGuiadas v q t l)).val

def sigueTableroYLineas {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) (b : ℝ) : Prop :=
  |tableroG v q t l-q|/q≤b ∧ ∀ i z,(∀ e∈l,llaveDeLinea i e≠llaveDeLinea i z)→
    |tableroG v q t l-q|/q+|masaObservadaDeLinea v q t l i z-(masaDeLineaG v i z:ℝ)|≤b

theorem margenes_del_tablero_fisico {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (qp : 0<q) {b : ℝ} (small : b≤1/10) (err : sigueTableroYLineas v q t l b) :
    (9/10:ℝ)*q≤tableroG v q t l ∧ tableroG v q t l≤(11/10:ℝ)*q := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have bd:=(abs_le.mp ((div_le_iff₀ qr).mp (err.1.trans small)))
  constructor <;> linarith only [bd.1,bd.2]

theorem regularidad_del_padre_fisico {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (tq : t<q)
    (l : List (Cell n)) {b η : ℝ} (hp : 0≤η) (small : b≤1/10)
    (slack : ∀ i e,(masaDeLineaG v i e:ℝ)≤1-η) (err : sigueTableroYLineas v q t l b) :
    regionSeguraDelPaso v q t (some l) := by
  refine ⟨tq,(margenes_del_tablero_fisico v l qp small err).1,?_⟩
  intro i z
  by_cases hit : ∃ e∈l,llaveDeLinea i e=llaveDeLinea i z
  · rw [linea_ocupada_tiene_masa_observada_cero v l i z hit]; norm_num
  · have root : ∀ e∈l,llaveDeLinea i e≠llaveDeLinea i z:=fun e he eq=>hit ⟨e,he,eq⟩
    have bd:=err.2 i z root
    have w : 0≤|tableroG v q t l-q|/(q:ℝ):=by positivity
    linarith only [bd,w,le_abs_self (masaObservadaDeLinea v q t l i z-(masaDeLineaG v i z:ℝ)),slack i z,hp,small]

theorem observacion_de_tablero_constante {I : Type} {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (f : I→Cell n→ℝ) (i : I) (one : ∀ e,f i e=1) (pos : ∀ e j,0<fraccionVivaG v q t e j) :
    observacionFisica v q f (.inl i) t l=tableroG v q t l := by
  simp only [observacionFisica,tableroG]
  rw [normalizador_real_del_paso_G]
  congr 1
  funext e
  rw [one,mul_one,cuatro_familias_dan_el_peso_de_G v q t e (fun j=>(pos e j).le)]

theorem seguimiento_inicial_del_tablero {n} (v : Cell n→ℝ≥0) (q : ℕ) (mass : ∑ e,(v e:ℝ)=q)
    {b : ℝ} (bn : 0≤b) : sigueTableroYLineas v q 0 [] b := by
  have w : tableroG v q 0 []=q:=(W_inicia_con_la_masa_de_entrada v q).trans mass
  constructor
  · simpa only [w,sub_self,abs_zero,zero_div] using bn
  · intro i z _
    simpa only [w,Z_inicia_en_la_masa_de_su_linea,sub_self,abs_zero,zero_div,zero_add] using bn
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.regularidad_del_padre_fisico
#print axioms ArticuloA.Historias.observacion_de_tablero_constante
