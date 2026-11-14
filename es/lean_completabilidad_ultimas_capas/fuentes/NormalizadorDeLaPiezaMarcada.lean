import DifusionDeLosPesosIniciales
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita Revelado
noncomputable section
open Classical
variable {n q : ℕ}

def wCelda (u : ColorWeights ℝ≥0) (e : Cell n) := pesoDe (factores u.real) (tuplaReal e)
def wTupla (u : ColorWeights ℝ≥0) (a : Candidata n) := pesoDe (factores u.virtual) a
def Wreal (n : ℕ) (u : ColorWeights ℝ≥0) := ∑ e : Cell n,wCelda u e
def Wvirtual (n : ℕ) (u : ColorWeights ℝ≥0) := ∑ a : Candidata n,wTupla u a
def logColor (n : ℕ) (u : ColorWeights ℝ≥0) (v : Pieza n) := if esReal v then Real.log (Wreal n u) else Real.log (Wvirtual n u)
def corteFisico (n : ℕ) (hn : 2≤n) := Rangos.corte (2*n-1-1) (by omega)
def restoRango (n : ℕ) (hn : 2≤n) (A : ℝ) := 4+(4+60*A)*(corteFisico n hn:ℝ)

structure Difusos (n : ℕ) (u : ColorWeights ℝ≥0) (A : ℝ) where
  MR : ℝ
  MV : ℝ
  A0 : 0≤A
  mr0 : 0≤MR
  mv0 : 0≤MV
  rpos : 0<Wreal n u
  vpos : 0<Wvirtual n u
  capR : ∀ e : Cell n,wCelda u e≤MR
  capV : ∀ a : Candidata n,wTupla u a≤MV
  rdiff : MR*(↑(2*n-1):ℝ)^2≤A*Wreal n u
  vdiff : MV*(↑(2*n-1):ℝ)^4≤A*Wvirtual n u

theorem cota_de_pieza (P : Tablero n q) (C : Completion P) (p : Indice n) (hn : 2≤n)
    (u : ColorWeights ℝ≥0) (A : ℝ) (dif : Difusos n u A) (pos : 0<(elegido u (pieza P C p)).val) :
    (∑ m∈Finset.range (2*n-1),porRango (Finset.univ.erase p) m (fun T => Real.log (masaSegun P C u p T))) ≤
      (↑(2*n-1):ℝ)*logColor n u (pieza P C p)-4*(↑(2*n-1):ℝ)+restoRango n hn A := by
  have card : (Finset.univ.erase p).card=2*n-1-1 := by simp
  have D : 0<(Finset.univ.erase p).card := by rw [card]; omega
  have cut : Rangos.corte (Finset.univ.erase p).card D = corteFisico n hn := by unfold corteFisico; congr
  have rhs : 4+6*(10*A)=4+60*A := by ring
  cases eq : pieza P C p with
  | real e =>
    have inj : Function.Injective (@tuplaReal n) := by
      intro y z h
      have a := congrArg Fin.val (congrFun h 0)
      have b := congrArg Fin.val (congrFun h 1)
      exact Prod.ext (Fin.ext a) (Fin.ext b)
    have mark : otros P C p (tuplaReal e)=∅ := (solo_la_marcada P C p _).mpr (fun i =>
      Fin.ext (congrArg (fun z => edgeOf z i) eq).symm)
    have bound : (Finset.univ.filter (fun e : Cell n => (otros P C p (tuplaReal e)).card≠4)).card≤10*(2*n-1)^1 :=
      (reales_excepcionales P C p).trans (by rw [pow_one]; omega)
    have wp : 0<wCelda u e := by
      rw [eq] at pos
      change 0<(weights masas u.real (numeros (tuplaReal e))).val at pos
      rwa [cuatro_pesos] at pos
    have nn (z : Cell n) : 0≤wCelda u z := by unfold wCelda pesoDe factores; positivity
    have r := rango_fisico_con_difusion P C p tuplaReal inj 1 (by decide) (wCelda u) nn
      (Wreal n u) dif.MR A dif.rpos dif.mr0 dif.A0 rfl dif.capR dif.rdiff bound ⟨e,mark,wp⟩ D
    simpa only [masaSegun,eq,logColor,esReal,if_true,cut,rhs,restoRango,add_assoc,wCelda] using r
  | virtual g =>
    let a := fun i => vertice P C i p
    have mark : otros P C p a=∅ := (solo_la_marcada P C p a).mpr (fun _ => rfl)
    have wp : 0<wTupla u a := by
      have same : numeros a=g := congrArg edgeOf eq
      rw [eq] at pos
      change 0<(weights masas u.virtual g).val at pos
      rwa [←same,cuatro_pesos] at pos
    have nn (z : Candidata n) : 0≤wTupla u z := by unfold wTupla pesoDe factores; positivity
    have r := rango_fisico_con_difusion P C p id Function.injective_id 3 (by decide) (wTupla u) nn
      (Wvirtual n u) dif.MV A dif.vpos dif.mv0 dif.A0 rfl dif.capV dif.vdiff
      (virtuales_excepcionales P C p) ⟨a,mark,wp⟩ D
    simpa only [masaSegun,eq,logColor,esReal,Bool.false_eq_true,if_false,id_eq,cut,rhs,restoRango,add_assoc,wTupla] using r
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cota_de_pieza
