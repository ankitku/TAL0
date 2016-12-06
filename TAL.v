(** * TAL-0 Typed Assembly Language *)

(** Based on paper by Greg Morrisett , TAL-0 is the design of a RISC-style typed assembly language which focuses on control-flow safety. This post provides a mechanized metatheory, particularly a machine checked proof of soundness of the TAL-0 type system as proposed by the author in section 4.2.10 of the book Advanced Topics in Types and Programming Languages.  *)

(** The TAL-0 language runs on an abstract machine which is represented by 3 components :

1. A heap H which is a finite, partial map from labels to heap values

2. a register file R which is a total map from registers to values, and 

3. a current instruction sequence I.  
*)

Require Import Bool Arith Vector LibTactics.
Require Import Maps.

Definition registers := total_map nat.
Definition empty_regs : registers := t_empty 0.
      
Inductive val : Type :=
 | ANum : nat -> val
 | AReg : nat -> val
 | ALab : nat -> val.

(** We denote addresses of instructions stored in the heap as labels. Unlike a typical machine where labels are resolved to some machine address, which are integers, we maintain a distinction between labels and arbit integers, as this complies with our goal to state and prove the control-flow safety i.e. we can only branch to a valid label, and not to any arbit integer. This will ensure that the machine never gets stuck while trying to do some invalid operation. *)
(*define relations for aeval , ieval*)
Fixpoint aeval (a : val) (R : registers) : nat :=
  match a with
 | ANum n => n
 | AReg d => R (Id d)
 | ALab l => l
  end.


Inductive instr : Type :=
 | IMov : forall d : nat,
    val -> instr
 | IAdd : forall d s : nat,
    instr
 | ISub : forall d v : nat,
    instr
 | IIf : forall d : nat,
    val -> instr.

Inductive instr_seq : Type :=
 | ISeq : instr -> instr_seq -> instr_seq
 | IJmp : val -> instr_seq.

(** Simple Notations are chosen for the sake of clarity while writing programs.*)
Notation "'R(' d ')' ':=' a" :=
  (IMov d (ANum a)) (at level 60).
Notation "'R(' d ')' '+:=' 'R(' s ')'" :=
  (IAdd d s) (at level 60).
Notation "'R(' s ')' '-:=' v" :=
  (ISub s v) (at level 60).
Notation "i1 ;; i2" :=
  (ISeq i1 i2) (at level 80, right associativity).
Notation "'JIF' 'R(' d ')' v" :=
  (IIf d (ANum v)) (at level 70).
Notation "'JMP' v" :=
  (IJmp (ALab v)) (at level 80).
Notation "'JMP' 'R(' r ')'" :=
  (IJmp (AReg r)) (at level 80).

Check JIF R(1) 2.
Check R(1) := 10.
Check R(2) +:= R(1).
Check R(2) -:= 1.
Check R(2) +:= R(1) ;; R(2) -:= 1 ;; JMP 2.
Check JMP 2.
Check JMP R(2).

      
Definition heaps := partial_map instr_seq.
Definition empty_heap : heaps := empty.

(* Machine State *)
Inductive st : Type :=
 | St : heaps -> registers -> instr_seq -> st.

(** Evaluation of instructions is supposed to change the Machine State and thus some of its components H, R or I. These changes are posed as relations between initial and final state of the machine. *)
Inductive ieval : st -> st -> Prop :=
 | R_IMov : forall H R I d a,
    ieval (St H R (R(d) := a ;; I)) (St H (t_update R (Id d) a) I)
 | R_IAdd : forall H R I d s,
     ieval (St H R (R(d) +:= R(s) ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R + aeval (AReg s) R)) I)
 | R_ISub : forall H R I d v,
     ieval (St H R (R(d) -:= v ;; I)) (St H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) I)
 | R_IJmp_Succ : forall H R I' a l,
     l = (aeval a R) -> H (Id l) = Some I' -> ieval (St H R (JMP l)) (St H R I')
 | R_IJmpR_Succ : forall H R I' r,
     H (Id (R (Id r))) = Some I' -> ieval (St H R (JMP R(r))) (St H R I')
 | R_IJmp_Fail : forall H R I a,
     H (Id (aeval a R)) = None -> ieval (St H R I) (St H R I)
 | R_IIf_EQ : forall H R I I2 r v,
     aeval (AReg r) R = 0 -> (H (Id v)) = Some I2 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I2)
 | R_IIf_NEQ : forall H R I r v,
     aeval (AReg r) R <> 0 -> ieval (St H R (JIF R(r) v ;; I)) (St H R I)   
 | R_ISeq : forall st st' st'',
     ieval st st' -> ieval st' st'' -> ieval st st''.

(** Example of a program fragment that multiplies 2 numbers stored in registers 1 and 2 and stores their product in register 3, before finally looping in its final state register 4. *)
Definition init_heap := update (update (update empty_heap (Id 1) (R(3) := 0 ;; JMP 2)) (Id 2) (JIF R(1) 3 ;; R(2) +:= R(3) ;; R(1) -:= 1 ;; JMP 2) ) (Id 3) (JMP R(4)).

Definition init_regs : registers :=  (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 7) 3) (Id 1) 1) (Id 2) 2).
Definition final_regs : registers := (t_update (t_update (t_update  (t_update (t_update (t_update empty_regs (Id 5) 1) (Id 6) 2) (Id 4) 1) (Id 1) 0) (Id 2) 2) (Id 3) 2).

Eval compute in init_heap (Id (init_regs (Id 6))).

(* jump to a label proof *)
Example ieval_example1 : ieval (St init_heap init_regs
                          (R(3) := 0 ;; JMP 2))
                               (St init_heap (t_update init_regs (Id 3) 0)
                          (JIF R(1) 3 ;; R(2) +:= R(3) ;; R(1) -:= 1 ;; JMP 2)).
Proof.
  apply R_ISeq with (St init_heap (t_update init_regs (Id 3) 0) (IJmp (ALab 2))).
  apply R_IMov.
  apply R_IJmp_Succ with (a := ALab 2).
  simpl.
  reflexivity.
  unfold init_heap.
  rewrite update_neq.
  rewrite update_eq.
  reflexivity.
  rewrite <- beq_id_false_iff; trivial.
Qed.


(** The types consist of
1. int -> represents arbit integer stored in a register

2. reg -> a type constructor. Takes as input, the type of the register, to which this register is pointing.

3. code -> takes as input a typing context Γ, and gives type (code Γ) which is the type of an instruction sequence that expects type of the Register file to be Γ before it begins execution 

4. arrow -> represents type of a single instruction (excluding JMP), which expects register file of type Γ1 before execution, and changes it to Γ2 after it has executed.

5. T -> It is the super type. It is used to represent the type of a register in R, which contains the label of the instruction currently executing. Because in such a case, we have the equation : Γ (r) = code Γ, which in the absence of subtyping or polymorphic types can't be solved. Hence T is assigned the type for such a register as it subsumes all types including itself. When we jump through a register of type T, we forget the type assigned to it, and reassign T to it.
Morrisett's paper uses the polymorphic type for due to some more benefits it affords. However we have used T type for its simplicity.
 *)

Inductive ty : Type :=
 | int : ty
 | reg : ty -> ty
 | code : partial_map ty -> ty
 | arrow : partial_map ty -> partial_map ty -> ty
 | True : ty.


Definition context := partial_map ty.

(* register file types *)
Definition empty_Gamma : context := empty.

(* heap types *)
Definition empty_Psi : context := empty.

(** The Typing Rules *)
(** Ψ is a partial map containing types of instruction sequences. As all instruction sequences end in a JMP statement, all valid values in Ψ are Some (code Γ) where Γ is the initial type state of register expected by that instruction sequence. Now, typing rules may require presence of either both Ψ and Γ, or only Ψ or neither. Hence, we introduce a combined context structure, that handles all the 3 cases. *)
Inductive cmbnd_ctx :=
 | EmptyCtx : cmbnd_ctx
 | PsiCtx : context -> cmbnd_ctx
 | PsiGammaCtx : context -> context -> cmbnd_ctx.

(** Typing rules for arithmetic expressions *)
Inductive ahas_type : cmbnd_ctx -> val -> ty -> Prop :=
 | S_Int : forall Ψ n,
     ahas_type (PsiCtx Ψ) (ANum n) int
 | S_Lab : forall Ψ Γ l v R,
     Ψ (Id l) = Some (code Γ) -> l = aeval (ALab v) R -> ahas_type (PsiCtx Ψ) (ALab v) (code Γ)
 | S_Reg : forall Ψ Γ r,
     Γ (Id r) = Some (reg int) -> ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg int)
 | S_RegV : forall Ψ Γ r,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg (code Γ))
 | S_RegT : forall Ψ Γ r,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg r) True
 | S_Val : forall Ψ Γ a tau,
     ahas_type (PsiCtx Ψ) a tau -> ahas_type (PsiGammaCtx Ψ Γ) a tau.

Hint Constructors ahas_type.

(** Typing rules for instructions *)
Inductive ihas_type : cmbnd_ctx -> instr -> ty -> Prop :=
 | S_Mov : forall Ψ Γ R d a tau,
    ahas_type (PsiGammaCtx Ψ Γ) a tau -> ahas_type (PsiGammaCtx Ψ Γ) (AReg d) (reg tau) -> (update Γ (Id d) (reg tau)) = Γ -> ihas_type (PsiCtx Ψ) (R(d) := aeval a R) (arrow Γ Γ)
 | S_Add : forall Ψ Γ d s,
    ahas_type (PsiGammaCtx Ψ Γ) (AReg s) (reg int) -> ahas_type (PsiGammaCtx Ψ Γ) (AReg d) (reg int) -> update Γ (Id d) (reg int) = Γ -> ihas_type (PsiCtx Ψ) (R(d) +:= R(s)) (arrow Γ Γ)
 | S_Sub : forall Ψ Γ s a v,
      ahas_type (PsiGammaCtx Ψ Γ) a int -> ahas_type (PsiGammaCtx Ψ Γ) (AReg s) (reg int) -> a = ANum v -> ihas_type (PsiCtx Ψ) (R(s) -:= v) (arrow Γ Γ)
 | S_If :  forall Ψ Γ r v,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg int) -> ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) -> ihas_type (PsiCtx Ψ) (JIF R(r) v) (arrow Γ Γ).
Hint Constructors ihas_type.


Inductive iseq_has_type : cmbnd_ctx -> instr_seq -> ty -> Prop :=
 | S_Jmp :  forall Ψ Γ v,
     ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) -> iseq_has_type (PsiCtx Ψ) (JMP v) (code Γ)
 | S_JmpT :  forall Ψ Γ v,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg v) True -> iseq_has_type (PsiCtx Ψ) (JMP R(v)) (code Γ)
 | S_Seq :  forall Ψ i1 i2 Γ Γ2,
     ihas_type (PsiCtx Ψ) i1 (arrow Γ Γ2) -> iseq_has_type (PsiCtx Ψ) i2 (code Γ2) -> iseq_has_type (PsiCtx Ψ) (ISeq i1 i2) (code Γ).                                           Hint Constructors iseq_has_type.



Definition init_Gamma : context := update (update (update (update empty_Gamma (Id 1) (reg int)) (Id 2) (reg int)) (Id 3) (reg int)) (Id 4) True.
Check init_Gamma.
Hint Unfold init_Gamma.

Definition init_Psi : context := update (update (update empty_Psi (Id 1) (code init_Gamma))(Id 3) (code init_Gamma)) (Id 2) (code init_Gamma).
Hint Unfold init_Psi.


Ltac match_map := repeat (try rewrite update_neq; try rewrite update_eq; try reflexivity).
Ltac inequality := (rewrite <- beq_id_false_iff; trivial).
Ltac crush_map := match_map ; inequality; try reflexivity.

Ltac rewrite_hyp :=
     match goal with
       | [ H : ?n = _ |- context[?n] ] => rewrite H
     end.

Ltac crush_generic :=
  repeat match goal with
         | [ H : ?T |- ?T    ] => exact T
         | [ |- ?T = ?T ] => reflexivity
         | [ |- True         ] => constructor
         | [ |- _ /\ _       ] => constructor
         | [ |- _ /\ _ -> _  ] => intro
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ |- nat -> _     ] => intro
         | _ => rewrite_hyp || eauto || jauto
         end.

Ltac crush :=
  repeat (crush_generic; match goal with
                         | [ |- update _ _ _ _ = _ ] => crush_map
                         | [ |- init_Gamma _ = _ ] => unfold init_Gamma
                         | [ |- init_Psi _ = _ ] => unfold init_Psi
                         | [ |- ieval _ _ ] => constructor; auto
                         | [ |- ihas_type _ _ _] => constructor; auto
                         | [ |- ?T -> False  ]  => assert T
                         | _ => try subst; trivial
                         end).
    


Example heap_2_type : forall I (R : registers), (init_heap (Id 2)) = Some I -> iseq_has_type (PsiCtx init_Psi) I (code init_Gamma).
Proof.
  intros.
  unfold init_heap in H.
  rewrite update_neq in H.
  rewrite update_eq in H.
  symmetry in H.
  inversion H.
  apply S_Seq with (Γ2 := init_Gamma).
  crush.
  constructor; auto.
  apply S_Lab with (l := 3) (R := R).
  crush.
  trivial.
  apply S_Seq with (Γ2 := init_Gamma).
  constructor; auto.
  crush.
  apply update_same.
  crush.
  apply S_Seq with (Γ2 := init_Gamma).
  unfold init_Psi.
  apply S_Sub with (a := ANum 1).
  unfold init_Psi.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  constructor; auto.
  apply S_Lab with (l := 2) (R := R).
  crush.
  trivial.
  trivial.
  rewrite <- beq_id_false_iff.
  trivial.
Qed.
                   
(** Typing rule for register file *)
Inductive Rhas_type : cmbnd_ctx -> registers -> context -> Prop :=
| S_Regfile : forall Ψ Γ R r tau a,
    (Γ (Id r)) = Some tau -> aeval a R = R (Id r) -> ahas_type (PsiGammaCtx Ψ Γ) a tau -> Rhas_type (PsiCtx Ψ) R Γ.

Hint Constructors Rhas_type.

(** Typing rule for Heap *)
Inductive Hhas_type : cmbnd_ctx -> heaps -> context -> Prop :=
| S_Heap : forall Ψ H,
    (forall l tau, exists is, Ψ (Id l) = Some tau /\ H (Id l) = Some is /\ iseq_has_type (PsiCtx Ψ) is tau) -> Hhas_type EmptyCtx H Ψ.

Hint Constructors Hhas_type.

(** Typing rule for a valid Machine State *)
Inductive M_ok : cmbnd_ctx -> heaps -> registers -> instr_seq -> Prop :=
| S_Mach : forall H R Is Ψ Γ,
    Hhas_type EmptyCtx H Ψ -> Rhas_type (PsiCtx Ψ) R Γ -> iseq_has_type (PsiCtx Ψ) Is (code Γ) -> M_ok EmptyCtx H R Is.

Hint Constructors M_ok.

(** We will require some Canonical Values Lemmas in our proof of Soundness *)
Lemma Canonical_Values_Int : forall H Ψ Γ v tau,
    Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) v tau -> tau = int -> exists n, v = ANum n.
Proof.
  intros.
  subst.
  inversion H1.
  inversion H6.
  exists n.
  crush.
Qed.


Lemma Canonical_Values_Reg :forall H Ψ Γ r R,
    Hhas_type EmptyCtx H Ψ -> Rhas_type (PsiCtx Ψ) R Γ -> ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg int) -> exists (n : nat), R (Id r) = n.
Proof.
  intros.
  exists (R (Id r)).
  crush.
Qed.

Lemma Canonical_Values_label1 : forall H Ψ Γ v,
    Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) ->  Ψ (Id v) = Some (code Γ) -> exists is, H (Id v) = Some is /\ iseq_has_type (PsiCtx Ψ) is (code Γ).
Proof.
  intros.
  inversion H0.
  inversion H1.
  inversion H7.
  simpl in H5.
  specialize H4 with ( l := v) (tau := code Γ).
  destruct H4 as [i G].
  exists i.
  crush.
Qed.

Lemma Canonical_Values_label2 : forall H Ψ Γ R r,
    Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) (AReg r) True -> exists is, H (Id (R (Id r))) = Some is /\ iseq_has_type (PsiCtx Ψ) is (code Γ).
Proof.
  intros.
  inversion H0.
  inversion H1.
  specialize H3 with ( l := R (Id r)) (tau := (code Γ)).
  destruct H3 as [i G].
  exists i.
  apply G.
  specialize H3 with ( l := R (Id r)) (tau := (code Γ)).
  destruct H3 as [i G].
  exists i.
  crush.
 Qed.

(** Finally the proof of Soundness *)
Theorem Soundness : forall H R Is,
    M_ok EmptyCtx H R Is -> exists H' R' Is', ieval (St H R Is) (St H' R' Is') /\ M_ok EmptyCtx H' R' Is'.
Proof.
  intros.
  inversion H0 ; induction Is; inverts H4.
  induction i; inversion H12;
   try match goal with
    | [H : Γ = Γ2 |- _ ] => symmetry in H
    end;
    try subst.


  (* ISeq IMov I *)
  exists H (t_update R (Id d) (aeval a R1)) Is.
  crush.
  apply S_Mach with (Ψ := Ψ) (Γ := Γ).
  crush.
  apply S_Regfile with (r := d) (tau := reg tau) (a := AReg d).
  rewrite <- H16.
  rewrite update_eq.
  crush.
  crush.
  crush.
  crush.
  
  (* ISeq IAdd I *)
  exists H (t_update R (Id d) (aeval (AReg d) R + aeval (AReg s) R)) Is.
  split.
  crush.
  apply S_Mach with (Ψ := Ψ) (Γ := Γ).
  crush.
  apply S_Regfile with (a := AReg d) (r := d) (tau := reg int).
  rewrite <- H16; apply update_eq.
  crush.
  crush.
  crush.
  
  (* ISeq ISub I *)
  exists H (t_update R (Id d) (aeval (AReg d) R - aeval (ANum v) R)) Is.
  split.
  crush.
  apply S_Mach with (Ψ := Ψ) (Γ := Γ).
  crush.
  apply S_Regfile with (a := AReg d) (r := d) (tau := reg int).
  inversion H15.
  crush.
  crush.
  inversion H15.
  crush.
  inversion H7.
  trivial.
  crush.
  crush.
  
  (* ISeq IIf I *)
  inversion H12.
  inversion H9.
  inversion H18.
  subst.
  simpl in H22.
  
  remember (R (Id d)) as rd; destruct rd.
  pose proof Canonical_Values_label1 H Ψ Γ v0 H2 H9 H22 as CVL1.
  destruct CVL1 as [Is' G].
  exists H R Is'.
  crush.

  exists H R Is.
  
  split.
  apply R_IIf_NEQ.
  simpl.
  symmetry in Heqrd; rewrite Heqrd.
  apply beq_nat_false_iff.
  trivial.
  crush.
  
  (*IJmp*)
  inversion H11; inversion H12.
  simpl in H17.
  subst.
  pose proof Canonical_Values_label1 H Ψ Γ v0 H2 H11 H16 as CVL1.
  destruct CVL1 as [Is G].

  exists H R Is.
  crush.
  apply R_IJmp_Succ with (a := ALab v0).
  crush.
  crush.
  
  (*IJmpT*)
  pose proof Canonical_Values_label2 H Ψ Γ R v0 H2 H11 as CVL3.
  destruct CVL3 as [Is G].

  exists H R Is.
  crush.
Qed.
