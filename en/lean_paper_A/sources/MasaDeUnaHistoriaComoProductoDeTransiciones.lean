import MasaAgregadaEnElSoporteDeLasHistorias
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

open Trayectoria.Adjunto
variable {X : Type}

def masaDeAtomo (xs : Atoms ℝ≥0 X) (x : X) : ℝ≥0 :=avg masas xs (mark masas (·=x))

theorem masa_de_la_historia_con_cabeza (P : ℕ→X→Atoms ℝ≥0 X) (t k : ℕ) (x y : X) (l : List X) :
    masaDeAtomo (rutas P t (k+1) x) (y::l)=masaDeAtomo (P t x) y*masaDeAtomo (rutas P (t+1) k y) l := by
  unfold masaDeAtomo
  rw [rutas,avg_bind]
  let tail:=avg masas (rutas P (t+1) k y) (mark masas (·=l))
  have row (z : X) : avg masas ((rutas P (t+1) k z).map (fun i=>(i.1,z::i.2))) (mark masas (·=y::l))
       =masas.mul tail (mark masas (·=y) z):=by
    rw [avg_push masas _ (List.cons z)]
    by_cases eq : z=y
    · subst z
      have eqp : (fun s : List X=>mark masas (·=y::l) (y::s))=mark masas (·=l):=by
        funext b; by_cases ok : b=l <;> simp [mark,ok]
      rw [eqp]; simp [tail,mark,masas]
    · have eqp : (fun s : List X=>mark masas (·=y::l) (z::s))=fun _=>0:=by
        funext b; simp [mark,eq,masas]
      rw [eqp,E2.avg_constant]; simp [mark,eq,masas]
  simp_rw [row]
  rw [avg_mul]; exact mul_comm _ _

def costeDeHistoria (P : ℕ→X→Atoms ℝ≥0 X) (t : ℕ) (x : X) : List X→ℝ
  | []=>0
  | y::l=> -log (masaAgregada (P t x) y)+costeDeHistoria P (t+1) y l

theorem masa_positiva_identifica_el_coste (P : ℕ→X→Atoms ℝ≥0 X) (t k : ℕ) (x : X) (l : List X)
    (length : l.length=k) (nz : masaAgregada (rutas P t k x) l≠0) :
    -log (masaAgregada (rutas P t k x) l)=costeDeHistoria P t x l := by
  induction l generalizing t k x with
  | nil=>
    have eq : k=0:=by simpa using length.symm
    subst k
    simp [costeDeHistoria,masaAgregada,rutas,avg_point,mark,masas]
  | cons y l ih=>
    have eq : k=l.length+1:=by simpa using length.symm
    subst k
    have fac : masaAgregada (rutas P t (l.length+1) x) (y::l)=
       masaAgregada (P t x) y*masaAgregada (rutas P (t+1) l.length y) l:=
      congrArg NNReal.toReal (masa_de_la_historia_con_cabeza P t l.length x y l)
    simp only [List.length_cons] at nz ⊢
    rw [fac] at nz ⊢
    have nn:=mul_ne_zero_iff.mp nz
    rw [Real.log_mul nn.1 nn.2,neg_add,costeDeHistoria,ih (t+1) l.length y rfl nn.2]

theorem entropia_de_las_historias_como_coste_del_camino (P : ℕ→X→Atoms ℝ≥0 X) (t k : ℕ) (x : X) :
    let xs:=rutas P t k x
    let S:=(xs.map Prod.snd).toFinset
    (∑ l∈S,-(masaAgregada xs l*log (masaAgregada xs l)))=
       ∑ l∈S,masaAgregada xs l*costeDeHistoria P t x l := by
  intro xs S
  apply Finset.sum_congr rfl
  intro l hl
  obtain ⟨a,ha,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp hl)
  have length : l.length=k:=eq ▸ (rutas_siguen_su_ley P t k x a ha).2
  by_cases nz : masaAgregada xs l=0
  · simp [nz]
  · rw [←masa_positiva_identifica_el_coste P t k x l length nz]
    ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_de_las_historias_como_coste_del_camino
