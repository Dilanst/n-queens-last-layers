import MediaDelCambioDeMasaEnElPasoReal
import PesoTemporalDeTresOCuatroFamilias
namespace ArticuloA.Historias
open Repair Trayectoria Trayectoria.ProfileKernel RealFinita
open scoped NNReal BigOperators
noncomputable section
open Classical

private theorem sumar_sobre_las_opciones {n} (B : List (Cell n)) (nd : B.Nodup)
    (l : List (Cell n)) (v : Cell n→ℝ≥0) (q t : ℕ) (f : Cell n→ℝ) :
    media ((B.filter (fun e=>decide (v e ≠ 0 ∧ ∀ c∈l,compatible e c))).map
      (fun e=>(pesoGuiado v q t e,e))) f=
      ∑ e∈B.toFinset,masaVivaEn l (fun b=>(pesoGuiado v q t b:ℝ)*f b) e := by
  induction B with
  | nil=>simp [media]
  | cons b B ih=>
    have h:=List.nodup_cons.mp nd
    rw [List.toFinset_cons,Finset.sum_insert (by simpa using h.1)]
    by_cases live : ∀ c∈l,compatible b c
    · by_cases nonzero : v b≠0
      · have ok : decide (v b≠0 ∧ ∀ c∈l,compatible b c)=true:=decide_eq_true ⟨nonzero,live⟩
        rw [List.filter_cons_of_pos (p:=fun e=>decide (v e≠0 ∧ ∀ c∈l,compatible e c)) (a:=b) ok,List.map_cons,media,ih h.2]
        simp only [masaVivaEn,if_pos live]
      · have absent : v b=0:=not_ne_iff.mp nonzero
        have no : ¬decide (v b≠0 ∧ ∀ c∈l,compatible b c)=true:=fun e=>nonzero (of_decide_eq_true e).1
        rw [List.filter_cons_of_neg (p:=fun e=>decide (v e≠0 ∧ ∀ c∈l,compatible e c)) (a:=b) no,ih h.2]
        have zero : pesoGuiado v q t b=0:=by simp [pesoGuiado,absent]
        simp only [masaVivaEn,if_pos live,zero,NNReal.coe_zero,zero_mul,zero_add]
    · have no : ¬decide (v b≠0 ∧ ∀ c∈l,compatible b c)=true:=fun e=>live (of_decide_eq_true e).2
      rw [List.filter_cons_of_neg (p:=fun e=>decide (v e≠0 ∧ ∀ c∈l,compatible e c)) (a:=b) no,ih h.2]
      simp only [masaVivaEn,if_neg live,zero_add]

theorem observable_real_sobre_las_opciones {n} (v : Cell n→ℝ≥0) (q t : ℕ)
    (l : List (Cell n)) (f : Cell n→ℝ) :
    media (opcionesGuiadas v q t l) f=pesoObservable (fun b=>(pesoGuiado v q t b:ℝ)*f b) (some l) := by
  have eq:=sumar_sobre_las_opciones (board n) (board_unique n) l v q t f
  have all : (board n).toFinset=Finset.univ:=by ext b; simp [board_complete]
  rwa [all] at eq

theorem normalizador_real_del_paso_G {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) :
    (total masas (opcionesGuiadas v q t l)).val=pesoObservable (fun b=>(pesoGuiado v q t b:ℝ)) (some l) := by
  have m:=observable_real_sobre_las_opciones v q t l (fun _=>1)
  have one:=media_coe (opcionesGuiadas v q t l) (fun _=>1)
  change media _ (fun _=>(1:ℝ))=(total masas _).val at one
  rw [←one]
  simpa only [mul_one] using m

theorem probabilidad_de_pieza_como_cociente {n} (v : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (pos : total masas (opcionesGuiadas v q t l)≠0) (c : Cell n) :
    leyDePieza v q t l c=masaVivaEn l (fun b=>(pesoGuiado v q t b:ℝ)) c/(total masas (opcionesGuiadas v q t l)).val := by
  let S : Cell n→Prop:=fun b=>b=c
  let a:=pasoDeG v q t (some l)
  let b:=opcionesGuiadas v q t l
  have obs:=media_del_paso_fisico v q t l pos (fun y=>(mark masas (observaCabeza S) y).val)
  have obs':=(media_coe a (mark masas (observaCabeza S))).symm.trans obs
  have left : (avg masas a (mark masas (observaCabeza S))).val=leyDePieza v q t l c:=by
    rw [obs',Finset.sum_eq_single c]
    · simp [S,observaCabeza,mark,masas]
    · intro j _ ne; simp [S,observaCabeza,mark,masas,ne]
    · simp
  have numer:=observable_real_sobre_las_opciones v q t l (fun e=>(mark masas S e).val)
  have numer':=(media_coe b (mark masas S)).symm.trans numer
  have right : (avg masas b (mark masas S)).val=masaVivaEn l (fun e=>(pesoGuiado v q t e:ℝ)) c:=by
    rw [numer']; simp only [pesoObservable]
    rw [Finset.sum_eq_single c]
    · simp [S,masaVivaEn,mark,masas]
    · intro j _ ne; simp [S,ne,masaVivaEn,mark,masas]
    · simp
  rw [←left,←right]
  exact congrArg NNReal.toReal (G_pone_una_reina_con_probabilidad_V_sobre_W v q t l S pos)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.probabilidad_de_pieza_como_cociente
#print axioms ArticuloA.Historias.normalizador_real_del_paso_G
