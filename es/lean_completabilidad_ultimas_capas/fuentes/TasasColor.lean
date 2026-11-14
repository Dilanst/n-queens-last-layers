import TasaVirtual
namespace ArticuloA.Trayectoria.E2
open ArticuloA ArticuloA.Repair ArticuloA.Corte ProfileKernel
variable {α : Type} (s : ProfileScale α)

def realDegree {n} (x : State n) (u : ColorWeights α) (v : Vertex) :=
  s.sum (board n) (fun e => if available x (lines e) && hitsVertex (lines e) v then weights s u.real (lines e) else s.zero)

def colourAt {n} (real : Bool) (v : Vertex) : Choice n → Bool
  | .real e => real && hitsVertex (lines e) v
  | .virtual g => !real && hitsVertex g v
  | .fail => false

private theorem take_scale {ι} (L : List ι) (w : ι → α) (ok : ι → Bool) (a b : α) :
    s.sum L (fun i => if ok i then s.mul a (s.mul b (w i)) else s.zero) =
      s.mul a (s.mul b (s.sum L (fun i => if ok i then w i else s.zero))) := by
  have swap (i : ι) : (if ok i then s.mul a (s.mul b (w i)) else s.zero) =
      s.mul (if ok i then w i else s.zero) (s.mul a b) := by
    cases ok i with
    | false => simp [s.mulComm,s.mulZero]
    | true => change s.mul a (s.mul b (w i)) = s.mul (w i) (s.mul a b)
              rw [←s.mulAssoc,s.mulComm (s.mul a b)]
  rw [funext swap,Cart.sum_scale,s.mulComm,s.mulAssoc]

private theorem sum_nilval {ι} (L : List ι) : s.sum L (fun _ => s.zero) = s.zero := by
  induction L with
  | nil => rfl
  | cons i L ih => change s.add s.zero (s.sum L _) = _; rw [s.zero_add,ih]

theorem real_rate {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (v : Vertex) :
    meanN s (choices s x u inv) (fun a => indicator (colourAt true v a = true)) =
      s.mul (quota s x inv x.reals) (s.mul (inv (total s (realChoices s x u))) (realDegree s x u v)) := by
  classical
  rw [regular_row s x u inv rr vv,mean_append,event_on_list,event_on_list]
  simp only [colourAt,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,and_false,
    if_false,sum_nilval,s.comm _ s.zero,s.zero_add]
  have eq := take_scale s (board n) (fun e => weights s u.real (lines e))
    (fun e => available x (lines e) && hitsVertex (lines e) v) (quota s x inv x.reals) (inv (total s (realChoices s x u)))
  simpa only [Bool.and_eq_true,realAtom,realDegree] using eq

theorem virtual_rate {n} (x : State n) (u : ColorWeights α) (inv : α → α)
    (rr : total s (realChoices s x u) ≠ s.zero) (vv : total s (virtualChoices s x u) ≠ s.zero)
    (v : Vertex) :
    meanN s (choices s x u inv) (fun a => indicator (colourAt false v a = true)) =
      s.mul (quota s x inv x.virtuals) (s.mul (inv (total s (virtualChoices s x u))) (s.four (Cart.constrainedPart s x u v))) := by
  classical
  rw [regular_row s x u inv rr vv,mean_append,event_on_list,event_on_list]
  simp only [colourAt,Bool.not_false,Bool.false_and,Bool.true_and,Bool.false_eq_true,and_false,
    if_false,sum_nilval,s.zero_add]
  rw [← Cart.hit_weight]
  have eq := take_scale s (virtualEdges (2*n-1)) (weights s u)
    (fun g => available x g && hitsVertex g v) (quota s x inv x.virtuals) (inv (total s (virtualChoices s x u)))
  simpa only [Bool.and_eq_true,virtAtom] using eq

end ArticuloA.Trayectoria.E2
#print axioms ArticuloA.Trayectoria.E2.real_rate
#print axioms ArticuloA.Trayectoria.E2.virtual_rate
