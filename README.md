 Based on paper by Greg Morrisett , TAL-0 is the design of a RISC-style typed assembly language which focuses on control-flow safety. This post provides a mechanized metatheory, particularly a machine checked proof of soundness of the TAL-0 type system as proposed by the author in section 4.2.10 of the book Advanced Topics in Types and Programming Languages.

 The TAL-0 language runs on an abstract machine which is represented by 3 components :

1. A heap H which is a finite, partial map from labels to heap values

2. a register file R which is a total map from registers to values, and 

3. a current instruction sequence I.  

An example state of the abstact machine is shown below:
<img src="http://i288.photobucket.com/albums/ll170/_ankitku/TAL0/TAl_zpsq0tw1ps8.png" height: 70%;" />

We denote addresses of instructions stored in the heap as labels. Unlike a typical machine where labels are resolved to some machine address, which are integers, we maintain a distinction between labels and arbitrary integers, as this complies with our goal to state and prove the control-flow safety i.e. we can only branch to a valid label, and not to any arbitrary integer. This will ensure that the machine never gets stuck while trying to do some invalid operation.

TAL-0 does not have expressions. It has operands on which instructions (like ADD, MOV etc.) operate. Some instructions act on Registers like "JMP R(d)". We use “value” to refer to an operand that is not a register. Such values include ANum (integer), ALab (label pointing to an instruction sequence in the heap) or AReg (value stored in a register, not the register itself). Following are the definitions for such values :

```coq
Inductive val : Type :=
 | ANum : nat -> val
 | AReg : nat -> val
 | ALab : nat -> val.
```

aeval function returns nat stored in the value.
```
Fixpoint aeval (a : val) (R : registers) : nat :=
  match a with
 | ANum n => n
 | AReg d => R (Id d)
 | ALab l => l
  end.
```
State of the machine is defined using the triple H (Heap), R(Register File) and Is(Current executing instruction sequence) :
```coq
Inductive st : Type :=
 | St : heaps -> registers -> instr_seq -> st.
```

Instructions are defined as follows :
```coq
Inductive instr : Type :=
 | IMov : forall d : nat,
    val -> instr
 | IAdd : forall d s : nat,
    instr
 | ISub : forall d v : nat,
    instr
 | IIf : forall d : nat,
    val -> instr.
```
And instruction sequences are defined in such a way that a sequence always has to end in a JMP.
```coq
Inductive instr_seq : Type :=
 | ISeq : instr -> instr_seq -> instr_seq
 | IJmp : val -> instr_seq.
```

Evaluation of instructions is supposed to change the Machine State and
thus some of its components H, R or Is. These changes are recorded as
relations between initial and final state of the machine.
```coq
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
```


##The Type System of TAL-0

The types consist of

1. int -> represents arbitrary integer stored in a register

2. reg -> a type constructor. Takes as input, the type of the register, to which this register is pointing.

3. code -> takes as input a typing context Gamma, and gives type (code Gamma) which is the type of an instruction sequence that expects type of the Register file to be Gamma before it begins execution 

4. arrow -> represents type of a single instruction (excluding JMP), which expects register file of type Gamma1 before execution, and changes it to Gamma2 after it has executed.

5. True (T in unicode) -> It is the super type. It is used to represent the type of a register in R, which contains the label of the instruction currently executing. Because in such a case, we have the equation : Gamma (r) = code Gamma, which in the absence of subtyping or polymorphic types can't be solved. Hence T is assigned the type for such a register as it subsumes all types including itself. When we jump through a register of type T, we forget the type assigned to it, and reassign T to it. Morrisett's paper uses the polymorphic type for due to some more benefits it affords. However we have used T type for its simplicity.

```coq
Inductive ty : Type :=
 | int : ty
 | reg : ty -> ty
 | code : partial_map ty -> ty
 | arrow : partial_map ty -> partial_map ty -> ty
 | True : ty.
```

Contexts are mappings between values and types. For values in Heaps,
their corresponding types are found in Psi, and for values in
Registers, their corresponding types are found in Gamma.
```coq
Definition context := partial_map ty.
```
#Typing Rules

Psi is a partial map containing types of instruction sequences. As all
instruction sequences end in a JMP statement, all valid values in Psi
are Some (code Gamma) where Gamma is the initial type state of
register expected by that instruction sequence. Now, typing rules may
require presence of either both Psi and Gamma, or only Psi or
neither. Hence, we introduce a combined context structure, that
handles all the 3 cases.

```coq
Inductive cmbnd_ctx :=
 | EmptyCtx : cmbnd_ctx
 | PsiCtx : context -> cmbnd_ctx
 | PsiGammaCtx : context -> context -> cmbnd_ctx.
```

<img
src="http://i288.photobucket.com/albums/ll170/_ankitku/TAL0/Screen%20Shot%202016-11-03%20at%2023.46.21_zpsi2vjatvk.png">

(the above image is taken from Morrisett's paper, defining the typing rules for TAL-0)

Typing rules for arithmetic expressions :
```coq
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
```

Typing rules for instructions :
```coq
Inductive ihas_type : cmbnd_ctx -> instr -> ty -> Prop :=
 | S_Mov : forall Ψ Γ R d a tau,
    ahas_type (PsiGammaCtx Ψ Γ) a tau -> ahas_type (PsiGammaCtx Ψ Γ) (AReg d) (reg tau) -> (update Γ (Id d) (reg tau)) = Γ -> ihas_type (PsiCtx Ψ) (R(d) := aeval a R) (arrow Γ Γ)
 | S_Add : forall Ψ Γ d s,
    ahas_type (PsiGammaCtx Ψ Γ) (AReg s) (reg int) -> ahas_type (PsiGammaCtx Ψ Γ) (AReg d) (reg int) -> update Γ (Id d) (reg int) = Γ -> ihas_type (PsiCtx Ψ) (R(d) +:= R(s)) (arrow Γ Γ)
 | S_Sub : forall Ψ Γ s a v,
      ahas_type (PsiGammaCtx Ψ Γ) a int -> ahas_type (PsiGammaCtx Ψ Γ) (AReg s) (reg int) -> a = ANum v -> ihas_type (PsiCtx Ψ) (R(s) -:= v) (arrow Γ Γ)
 | S_If :  forall Ψ Γ r v,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg int) -> ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) -> ihas_type (PsiCtx Ψ) (JIF R(r) v) (arrow Γ Γ).
```

Typing rules for instruction sequences :
```coq
 | S_Jmp :  forall Ψ Γ v,
     ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) -> iseq_has_type (PsiCtx Ψ) (JMP v) (code Γ)
 | S_JmpT :  forall Ψ Γ v,
     ahas_type (PsiGammaCtx Ψ Γ) (AReg v) True -> iseq_has_type (PsiCtx Ψ) (JMP R(v)) (code Γ)
 | S_Seq :  forall Ψ i1 i2 Γ Γ2,
     ihas_type (PsiCtx Ψ) i1 (arrow Γ Γ2) -> iseq_has_type (PsiCtx Ψ) i2 (code Γ2) -> iseq_has_type (PsiCtx Ψ) (ISeq i1 i2) (code Γ).
```

#Typing of Heaps, Registers and validity of machine
We say that machine is OK, i.e. in a valid state iff H has type Psi, R
has type Gamma and current instruction sequence being executed has type "code Gamma".
```coq
Inductive Rhas_type : cmbnd_ctx -> registers -> context -> Prop :=
 | S_Regfile : forall Ψ Γ R r tau a, 
   (Γ (Id r)) = Some tau -> aeval a R = R (Id r) -> ahas_type (PsiGammaCtx Ψ Γ) a tau -> Rhas_type (PsiCtx Ψ) R Γ.

Inductive Hhas_type : cmbnd_ctx -> heaps -> context -> Prop :=
  | S_Heap : forall Ψ H, 
    (forall l tau, exists is, Ψ (Id l) = Some tau /\ H (Id l) = Some is /\ iseq_has_type (PsiCtx Ψ) is tau) -> Hhas_type EmptyCtx H Ψ.

Inductive M_ok : cmbnd_ctx -> heaps -> registers -> instr_seq -> Prop :=
 | S_Mach : forall H R Is Ψ Γ, 
   Hhas_type EmptyCtx H Ψ -> Rhas_type (PsiCtx Ψ) R Γ -> iseq_has_type (PsiCtx Ψ) Is (code Γ) -> M_ok EmptyCtx H R Is.
```

Some canonical values lemmas we will need in proving Soundness of the
type system.
```coq
Lemma Canonical_Values_Int : forall H Ψ Γ v tau, 
      Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) v tau -> tau = int -> exists n, v = ANum n.

Lemma Canonical_Values_Reg :forall H Ψ Γ r R, Hhas_type EmptyCtx H Ψ -> Rhas_type (PsiCtx Ψ) R Γ -> ahas_type (PsiGammaCtx Ψ Γ) (AReg r) (reg int) -> exists (n : nat), R (Id r) = n.

Lemma Canonical_Values_label1 : forall H Ψ Γ v, 
      Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) (ALab v) (code Γ) ->  Ψ (Id v) = Some (code Γ) -> exists is, H (Id v) = Some is /\ iseq_has_type (PsiCtx Ψ) is (code Γ).

Lemma Canonical_Values_label2 : forall H Ψ Γ R r, 
      Hhas_type EmptyCtx H Ψ -> ahas_type (PsiGammaCtx Ψ Γ) (AReg r) True -> exists is, H (Id (R (Id r))) = Some is /\ iseq_has_type (PsiCtx Ψ) is (code Γ).
```

Proving safety of the type system requires proving

1. Progress : A well typed machine state (M_ok  M(H,R,Is)) doesn't get
stuck. eg. It will never try to jump to an arbitrary integer, which we
wanted as part of control flow safety.
2. Preservation : After each transition to a new machine state
M'(H',R',Is'), the new state is also well typed.

Hence the soundness theorem is stated as follows :
```coq
Theorem Soundness : forall H R Is,
    M_ok EmptyCtx H R Is -> exists H' R' Is', ieval (St H R Is) (St H' R' Is') /\ M_ok EmptyCtx H' R' Is'.
```

I would like to thank [Chris Casinghino][tyc] for his feedback on the first version of this post.


[src]:https://github.com/ankitku/TAL0

[tyc]:http://tyconmismatch.com/


