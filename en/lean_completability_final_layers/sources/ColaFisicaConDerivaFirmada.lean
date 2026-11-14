import ColaBilateralEnElMismoCamino
import BalanceEscaladoDeLaMalla
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Corte
noncomputable section
variable {X : Type} (S : ℕ→X→Atoms ℝ≥0 X) (F G : X→ℝ≥0)

def pasosConDeriva (U : ℝ≥0) (t : ℕ) (x : X) : List X→Prop
  | [] => True
  | y::ys => within masas (avg masas (S t x) F+G x) (avg masas (S t x) G+F x) U ∧
    pasosConDeriva U (t+1) y ys

theorem desvio_de_la_historia (U : ℝ≥0) (l : List X) (t : ℕ) (H : HistoryBook X ℝ≥0)
    (ok : pasosConDeriva S F G U t H.state l) :
    let H' := leerLibro S (fun _ => F) (fun _ => G) t H l
    let V := fun x => (F x:ℝ)-(G x:ℝ)
    |V (l.foldl (fun _ y => y) H.state)-V H.state-(saldo H'-saldo H)|≤l.length*(U:ℝ) := by
  intro H' V
  induction l generalizing t H with
  | nil => simp [H',leerLibro]
  | cons y l ih =>
    let J:=record masas S (fun _ => F) (fun _ => G) t H y
    have nextOk : pasosConDeriva S F G U (t+1) J.state l := ok.2
    have tail:=ih (t+1) J nextOk
    have base := (presupuesto_absoluto _ _ _).mp ok.1
    simp only [NNReal.coe_add] at base
    have direct : V y-V H.state-(saldo J-saldo H)=
        (avg masas (S t H.state) F).val+G H.state-((avg masas (S t H.state) G).val+F H.state) := by
      change _-_-((↑(H.pos+(F y+avg masas (S t H.state) G):ℝ≥0):ℝ)-
        ↑(H.neg+(G y+avg masas (S t H.state) F):ℝ≥0)-_)=_
      simp only [NNReal.coe_add,saldo,V]
      have alg (a b c d i j u v : ℝ) : (a-b)-(c-d)-((i+(a+v)-(j+(b+u)))-(i-j))=u+d-(v+c) := by ring
      exact alg _ _ _ _ _ _ _ _
    let Final:=leerLibro S (fun _ => F) (fun _ => G) (t+1) J l
    change |V (l.foldl (fun _ y => y) y)-V y-(saldo Final-saldo J)|≤_ at tail
    change |V (l.foldl (fun _ y => y) y)-V H.state-(saldo Final-saldo H)|≤_
    calc
      _ = |(V (l.foldl (fun _ y => y) y)-V y-(saldo Final-saldo J))+(V y-V H.state-(saldo J-saldo H))| :=
        congrArg abs (by ring)
      _ ≤ _ := abs_add_le .. 
      _ ≤ l.length*(U:ℝ)+U := add_le_add tail (by rw [direct]; exact base)
      _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem cola_del_valor_en_buenas_historias (U B : ℝ≥0) (V : X→Prop)
    (norm : ∀ t x,total masas (S t x)=1) (stable : ∀ t x,V x → ∀ i∈S t x,V i.2)
    (jump : ∀ t x,V x → ∀ i∈S t x,within masas (F i.2+avg masas (S t x) G) (G i.2+avg masas (S t x) F) B)
    (t T : ℕ) (x : X) (vx : V x) (θ a : ℝ) (tp : 0≤θ) (small : θ*B≤1) :
    let obs := fun y => (F y:ℝ)-(G y:ℝ)
    (avg masas (rutas S t T x) (mark masas (fun l => l.length=T ∧ pasosConDeriva S F G U t x l ∧
      a+T*(U:ℝ)≤|obs (l.foldl (fun _ y => y) x)-obs x|))).val ≤
      2*Real.exp ((T:ℝ)*(θ*B)^2-θ*a) := by
  intro obs
  have bound:=cola_de_prefijo S (fun _ => F) (fun _ => G) norm B V stable jump t T T le_rfl x vx θ a tp small
  apply le_trans _ bound
  apply NNReal.coe_le_coe.mpr
  apply avg_mono masas
  intro i _
  have subset {P Q : Prop} (inc : P→Q) : masas.le (mark masas (fun _ : Unit => P) ()) (mark masas (fun _ : Unit => Q) ()) := by
    classical
    by_cases hp : P
    · simp [mark,hp,inc hp,masas]
    · simp only [mark,hp,if_false]; exact zero_le _
  apply subset
  rintro ⟨len,good,large⟩
  have dev:=desvio_de_la_historia S F G U i.2 t (libroCero x) good
  have take : i.2.take T=i.2 := List.take_of_length_le (le_of_eq len)
  rw [take]
  have zero : saldo (libroCero x)=0 := by simp [saldo,libroCero]
  change |obs (i.2.foldl (fun _ y => y) x)-obs x-(saldo (leerLibro S (fun _ => F) (fun _ => G) t (libroCero x) i.2)-saldo (libroCero x))|≤_ at dev
  rw [zero,sub_zero,len] at dev
  have tri:=abs_sub_le (obs (i.2.foldl (fun _ y => y) x)-obs x) (saldo (leerLibro S (fun _ => F) (fun _ => G) t (libroCero x) i.2)) 0
  simp only [sub_zero] at tri
  linarith

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_del_valor_en_buenas_historias
