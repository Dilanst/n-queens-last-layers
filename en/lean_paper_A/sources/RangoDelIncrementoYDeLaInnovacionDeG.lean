import MediaDelCambioDeMasaEnElPasoReal
import CasillasQuePuedeEliminarUnaPieza
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped BigOperators NNReal
noncomputable section
open Classical

def gananciaPorTiempo {n} (l : List (Cell n)) (S : Finset (Cell n)) (a a' : Cell n→ℝ) : ℝ :=
  ∑ c∈S,(masaVivaEn l a' c-masaVivaEn l a c)

def perdidaPorLaPieza {n} (l : List (Cell n)) (S : Finset (Cell n)) (a' : Cell n→ℝ) (b : Cell n) : ℝ :=
  ∑ c∈S∩atacadasPor b,masaVivaEn l a' c

theorem cambio_como_ganancia_menos_perdida {n} (l : List (Cell n)) (S : Finset (Cell n))
    (a a' : Cell n→ℝ) (b : Cell n) :
    (∑ c∈S,(masaVivaEn (b::l) a' c-masaVivaEn l a c))=
      gananciaPorTiempo l S a a'-perdidaPorLaPieza l S a' b := by
  unfold gananciaPorTiempo perdidaPorLaPieza
  have sub : S∩atacadasPor b=S.filter (fun c=>¬compatible c b):=by ext; simp [atacadasPor]
  rw [sub,Finset.sum_filter,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [masa_viva_al_colocar]
  by_cases h : compatible c b <;> simp [h]

theorem cotas_de_la_perdida {n} (l : List (Cell n)) (S : Finset (Cell n))
    (a' : Cell n→ℝ) {L : ℝ} (lo : ∀ c,0≤a' c) (hi : ∀ c,a' c≤L) (lp : 0≤L) (b : Cell n) :
    0≤perdidaPorLaPieza l S a' b ∧
      perdidaPorLaPieza l S a' b≤((S∩atacadasPor b).card:ℝ)*L := by
  have bound (c) : 0≤masaVivaEn l a' c ∧ masaVivaEn l a' c≤L:=by
    unfold masaVivaEn; split
    · exact ⟨lo c,hi c⟩
    · exact ⟨le_rfl,lp⟩
  exact ⟨Finset.sum_nonneg (fun c _=>(bound c).1),(Finset.sum_le_sum
    (fun c (_ : c∈S∩atacadasPor b)=>(bound c).2)).trans (by simp)⟩

theorem centrar_en_un_intervalo_del_paso {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (Y : EstadoGuiado n→ℝ) {u w : ℝ}
    (range : ∀ b,u≤Y (some (b::l)) ∧ Y (some (b::l))≤w) (b : Cell n) :
    |Y (some (b::l))-media (pasoDeG v q t (some l)) Y|≤w-u := by
  rw [media_del_paso_fisico _ _ _ _ reg]
  let p:=leyDePieza v q t l
  have np:=ley_de_pieza_no_negativa v q t l
  have totalp : ∑ e,p e=1:=ley_de_pieza_normalizada v q t l reg
  have lo:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>mul_le_mul_of_nonneg_left (range e).1 (np e))
  have hi:=Finset.sum_le_sum (s:=Finset.univ) (fun e _=>mul_le_mul_of_nonneg_left (range e).2 (np e))
  change (∑ e,p e*u)≤_ at lo
  change _≤(∑ e,p e*w) at hi
  rw [←Finset.sum_mul,totalp,one_mul] at lo hi
  exact abs_le.mpr ⟨by linarith [(range b).1],by linarith [(range b).2]⟩

def deltaDeMasaEn {n} (l : List (Cell n)) (S : Finset (Cell n)) (a a' : Cell n→ℝ) : EstadoGuiado n→ℝ
  | some h=>∑ c∈S,(masaVivaEn h a' c-masaVivaEn l a c)
  | none=>0

theorem salto_centrado_del_tablero {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (a a' : Cell n→ℝ) {L : ℝ}
    (lo : ∀ c,0≤a' c) (hi : ∀ c,a' c≤L) (lp : 0≤L) (b : Cell n) :
    let Y:=deltaDeMasaEn l Finset.univ a a'
    |Y (some (b::l))-media (pasoDeG v q t (some l)) Y|≤4*n*L := by
  let D:=gananciaPorTiempo l Finset.univ a a'
  have bd:=centrar_en_un_intervalo_del_paso v q t l reg (deltaDeMasaEn l Finset.univ a a')
    (u:=D-4*n*L) (w:=D) (fun e=>by
      change _≤(∑ c,_) ∧ (∑ c,_)≤_
      rw [cambio_como_ganancia_menos_perdida]
      obtain ⟨nn,cap⟩:=cotas_de_la_perdida l Finset.univ a' lo hi lp e
      simp only [Finset.univ_inter] at cap
      have sz : ((atacadasPor e).card:ℝ)≤4*n:=by exact_mod_cast a_lo_sumo_cuatro_n e
      have c:=cap.trans (mul_le_mul_of_nonneg_right sz lp)
      exact ⟨by dsimp only [D]; linarith,by dsimp only [D]; linarith⟩) b
  linarith only [bd]

theorem salto_centrado_de_la_linea {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n) (a a' : Cell n→ℝ)
    {L : ℝ} (lo : ∀ c,0≤a' c) (hi : ∀ c,a' c≤L) (lp : 0≤L)
    (gain : 0≤gananciaPorTiempo l (fibraFisicaG i z) a a') (b : Cell n) :
    let S:=fibraFisicaG i z
    let Y:=fun y=>if fueraDeRaiz i z y then deltaDeMasaEn l S a a' y else 0
    |Y (some (b::l))-media (pasoDeG v q t (some l)) Y|≤gananciaPorTiempo l S a a'+3*L := by
  let S:=fibraFisicaG i z
  let Y:=fun y=>if fueraDeRaiz i z y then deltaDeMasaEn l S a a' y else 0
  have bd:=centrar_en_un_intervalo_del_paso v q t l reg Y (u:= -(3*L)) (w:=gananciaPorTiempo l S a a')
    (fun e=>by
      by_cases on : llaveDeLinea i e=llaveDeLinea i z
      · simp [Y,fueraDeRaiz,on,S,gain,lp]
      · simp only [Y,fueraDeRaiz,ne_eq,decide_not,deltaDeMasaEn,on,decide_false,Bool.not_false,if_true]
        rw [cambio_como_ganancia_menos_perdida]
        obtain ⟨nn,cap⟩:=cotas_de_la_perdida l S a' lo hi lp e
        have sz : ((S∩atacadasPor e).card:ℝ)≤3:=by exact_mod_cast a_lo_sumo_tres_de_una_linea i z e on
        have c:=cap.trans (mul_le_mul_of_nonneg_right sz lp)
        change 0≤gananciaPorTiempo l S a a' at gain
        constructor <;> linarith) b
  dsimp only
  exact bd.trans (by linarith)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.salto_centrado_del_tablero
#print axioms ArticuloA.Historias.salto_centrado_de_la_linea
