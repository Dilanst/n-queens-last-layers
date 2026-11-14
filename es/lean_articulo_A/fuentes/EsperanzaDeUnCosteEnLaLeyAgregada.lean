import MasaAgregadaEnElSoporteDeLasHistorias
import MediaDeUnaSumaDeMarcas
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
variable {X Y : Type}

theorem media_con_peso_agregado (xs : Atoms ℝ≥0 X) (f : X→ℝ) (S : Finset X)
    (cover : ∀ i∈xs,i.2∈S) : media xs f=∑ x∈S,masaAgregada xs x*f x := by
  induction xs with
  | nil=>change (0:ℝ)=∑ x∈S,(0:ℝ)*f x; simp
  | cons i l ih=>
    have inc:=cover i List.mem_cons_self
    have rest:=ih (fun a ha=>cover a (List.mem_cons_of_mem _ ha))
    have part x : masaAgregada (i::l) x=(if i.2=x then (i.1:ℝ) else 0)+masaAgregada l x:=by
      change ((i.1*mark masas (fun y=>y=x) i.2+avg masas l (mark masas (fun y=>y=x)):ℝ≥0):ℝ)=_
      by_cases eq : i.2=x <;> simp [masaAgregada,mark,masas,eq]
    simp_rw [part,add_mul]
    rw [Finset.sum_add_distrib,media,rest]
    congr 1
    rw [Finset.sum_eq_single i.2]
    · simp
    · intro b _ diff
      simp [Ne.symm diff]
    · exact fun no=>False.elim (no inc)

theorem media_de_union_de_listas (a b : Atoms ℝ≥0 X) (f : X→ℝ) :
    media (a++b) f=media a f+media b f := by
  induction a with
  | nil=>simp [media]
  | cons i _ ih=>simp [media,ih,add_assoc]

theorem media_con_factor_y_mapa (a : ℝ≥0) (xs : Atoms ℝ≥0 Y) (g : Y→X) (f : X→ℝ) :
    media (xs.map (fun i=>(a*i.1,g i.2))) f=(a:ℝ)*media xs (fun y=>f (g y)) := by
  induction xs with
  | nil=>simp [media]
  | cons i _ ih=>simp [media,ih]; ring

theorem media_de_una_eleccion_y_su_continuacion (xs : Atoms ℝ≥0 X) (K : X→Atoms ℝ≥0 Y)
    (f : Y→ℝ) : media (bindAtoms masas xs K) f=media xs (fun x=>media (K x) f) := by
  induction xs with
  | nil=>rfl
  | cons i rest ih=>
    change media (((K i.2).map (fun z=>(i.1*z.1,z.2)))++bindAtoms masas rest K) f=_
    rw [media_de_union_de_listas,ih]
    exact congrArg (·+media rest (fun x=>media (K x) f)) (media_con_factor_y_mapa i.1 (K i.2) (fun x=>x) f)

theorem media_de_una_funcion_tras_mapa (xs : Atoms ℝ≥0 Y) (g : Y→X) (f : X→ℝ) :
    media (xs.map (fun i=>(i.1,g i.2))) f=media xs (fun y=>f (g y)) := by
  simpa using media_con_factor_y_mapa (1:ℝ≥0) xs g f

theorem media_suma_de_dos_costes (xs : Atoms ℝ≥0 X) (f g : X→ℝ) :
    media xs (fun x=>f x+g x)=media xs f+media xs g := by
  induction xs with
  | nil=>simp [media]
  | cons i _ ih=>simp [media,ih]; ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_con_peso_agregado
#print axioms ArticuloA.Historias.media_de_una_eleccion_y_su_continuacion
