import IncidenciaDeCuatroLineasEnUnPaso
import LeyCondicionalDeLaPiezaEnElTablero
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped BigOperators NNReal
noncomputable section
open Classical

def masaVivaEn {n} (l : List (Cell n)) (a : Cell n→ℝ) (c : Cell n) : ℝ :=
  if ∀ d∈l,compatible c d then a c else 0

theorem masa_viva_al_colocar {n} (l : List (Cell n)) (a : Cell n→ℝ) (c b : Cell n) :
    masaVivaEn (b::l) a c=if compatible c b then masaVivaEn l a c else 0 := by
  by_cases free : compatible c b <;> simp [masaVivaEn,free]

theorem integral_de_la_masa_que_sobrevive {n} (l : List (Cell n)) (a p : Cell n→ℝ)
    (ley : ∑ b,p b=1) (c : Cell n) :
    ∑ b,p b*masaVivaEn (b::l) a c=
      masaVivaEn l a c*(1-(∑ i,riesgoDeLinea p c i)+3*p c) := by
  rw [←supervivencia_de_una_casilla p ley c,mul_comm,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [masa_viva_al_colocar]
  by_cases h : compatible c b <;> simp [h]

def pesoObservable {n} (a : Cell n→ℝ) : EstadoGuiado n→ℝ
  | none=>0
  | some l=>∑ c,masaVivaEn l a c

theorem deriva_fisica_de_masa_disponible {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (pos : total masas (opcionesGuiadas v q t l)≠0) (a a' : Cell n→ℝ) :
    let p:=leyDePieza v q t l
    media (pasoDeG v q t (some l)) (fun y=>pesoObservable a' y-pesoObservable a (some l))=
      ∑ c,(masaVivaEn l a' c*(1-(∑ i,riesgoDeLinea p c i)+3*p c)-masaVivaEn l a c) := by
  let p:=leyDePieza v q t l
  have norm : ∑ b,p b=1:=ley_de_pieza_normalizada v q t l pos
  rw [media_del_paso_fisico _ _ _ _ pos]
  change (∑ b,p b*((∑ c,masaVivaEn (b::l) a' c)-(∑ c,masaVivaEn l a c)))=_
  simp_rw [mul_sub,Finset.mul_sum]
  rw [Finset.sum_sub_distrib,Finset.sum_comm,Finset.sum_comm (f:=fun b c=>p b*masaVivaEn l a c),
    Finset.sum_sub_distrib]
  apply congrArg₂ (·-·)
  · apply Finset.sum_congr rfl; intro c _; exact integral_de_la_masa_que_sobrevive l a' p norm c
  · simp_rw [←Finset.sum_mul,norm,one_mul]

def fueraDeRaiz {n} (i : Fin 4) (z : Cell n) : EstadoGuiado n→Bool
  | some (b::_)=>decide (llaveDeLinea i b≠llaveDeLinea i z)
  | _=>false

theorem deriva_fisica_de_una_linea_congelada {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (pos : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z c : Cell n)
    (inc : llaveDeLinea i c=llaveDeLinea i z) (a a' : Cell n→ℝ) :
    let p:=leyDePieza v q t l
    media (pasoDeG v q t (some l)) (fun y=>if fueraDeRaiz i z y then
      (match y with | some s=>masaVivaEn s a' c | none=>0)-masaVivaEn l a c else 0)=
      masaVivaEn l a' c*(1-(∑ j,riesgoDeLinea p c j)+3*p c)-
        masaVivaEn l a c*(1-riesgoDeLinea p c i) := by
  let p:=leyDePieza v q t l
  have norm : ∑ b,p b=1:=ley_de_pieza_normalizada v q t l pos
  rw [media_del_paso_fisico _ _ _ _ pos]
  dsimp only
  rw [←integral_de_la_masa_que_sobrevive l a' p norm c]
  have diff : (∑ b : Cell n,if llaveDeLinea i b≠llaveDeLinea i c then p b else 0)=1-riesgoDeLinea p c i := by
    rw [←norm,riesgoDeLinea,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro b _
    by_cases e : llaveDeLinea i b=llaveDeLinea i c <;> simp [e]
  rw [←diff,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : llaveDeLinea i b=llaveDeLinea i c
  · have kill : ¬compatible c b:=fun e=>((compatible_iff_llaves _ _).mp e i) h.symm
    simp [fueraDeRaiz,←inc,h,masa_viva_al_colocar,kill]
  · simp [fueraDeRaiz,←inc,h,p,mul_sub,mul_comm]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_fisica_de_masa_disponible
#print axioms ArticuloA.Historias.deriva_fisica_de_una_linea_congelada
