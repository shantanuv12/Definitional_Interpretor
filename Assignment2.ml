exception Unmatch;;
exception EmptyStack;;
open List;;
type exp =Const of int
          | Bool of bool
          | Abs of exp
          | Var of string
          | Succ of exp
          | Pred of exp
          | Plus of exp * exp
          | Subtract of exp * exp
          | Mult of exp * exp
          | Div of exp * exp
          | Mod of exp * exp
          | Exp of exp * exp
          | Not of exp
          | And of exp * exp
          | Or of exp * exp
          | Imp of exp * exp
          | Equals of exp * exp
          | Grthan of exp * exp
          | Lesthan of exp * exp
          | Grteql of exp * exp
          | Leseql of exp * exp
          | Tup of exp list
          | Proj of exp * exp;;

type opcode =CONST of int
            | BOOL of bool
            | LOOKUP of string
            | ABS
            | PLUS
            | MINUS
            | MULT
            | DIV
            | MOD
            | SUCC
            | PRED
            | EXP
            | NOT
            | AND
            | OR
            | IMP
            | EQUALS
            | GRTHAN
            | LESTHAN
            | GRTEQL
            | LESEQL
            | TUP of opcode list list
            | PROJ;;

type answer=Integer of int| Boolean of bool | Tuple of answer list;;

let add (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1+n2)
|(_,_)-> raise Unmatch;;
let sub (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1-n2)
|(_,_)-> raise Unmatch;;
let mult (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1*n2)
|(_,_)-> raise Unmatch;;
let div (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1/n2)
|(_,_)-> raise Unmatch;;
let modulus (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (n1 mod n2)
|(_,_)-> raise Unmatch;;
let exp (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Integer (int_of_float(float_of_int(n1) ** float_of_int(n2)))
|(_,_)->raise Unmatch;;
let succ e1=match e1 with
Integer e1->Integer (e1+1)
|_-> raise Unmatch;;
let pred e1=match e1 with
Integer n1->Integer (n1+1)
|_-> raise Unmatch;;
let abs e1=match e1 with
Integer n1-> if n1>0 then Integer n1 else Integer (-n1)
|_->raise Unmatch;;
let andl (e1,e2) =match (e1,e2) with
(Boolean b1,Boolean b2)-> Boolean (b1 && b2)
|(_,_)->raise Unmatch;;
let orl (e1,e2) =match (e1,e2) with
(Boolean b1,Boolean b2)-> Boolean (b1 || b2)
|(_,_)->raise Unmatch;;
let notl e1=match e1 with
Boolean b->Boolean (not b)
|_->raise Unmatch;;
let implies (e1,e2)=match (e1,e2) with
(Boolean false,Boolean false)->Boolean true
|(Boolean false,Boolean true)->Boolean true
|(Boolean true,Boolean false)->Boolean false
|(Boolean true,Boolean true)->Boolean true
|(_,_)->raise Unmatch;;
let equals (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1=n2)
|(_,_)->raise Unmatch;;
let greater (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1>n2)
|(_,_)->raise Unmatch;;
let greateq (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1>=n2)
|(_,_)->raise Unmatch;;
let lesser (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1<n2)
|(_,_)->raise Unmatch;;
let lesseql (e1,e2)=match (e1,e2) with
(Integer n1,Integer n2)->Boolean (n1<=n2)
|(_,_)->raise Unmatch;;


let extract_int a=match a with
Integer n->n
| _->raise Unmatch;;

let rho x=match x with
"x"->Integer 4
| _->Integer 0;;

let rec eval rho e=match e with
Const n->Integer n
| Bool b-> Boolean b
| Var x-> rho x
| Abs n-> abs (eval rho n)
| Succ n-> succ (eval rho n)
| Pred n-> pred (eval rho n)
| Plus (n1,n2)-> add (eval rho n1,eval rho n2)
| Subtract (n1,n2)-> sub (eval rho n1,eval rho n2)
| Mult (n1,n2)-> mult (eval rho n1,eval rho n2)
| Div (n1,n2)-> div (eval rho n1,eval rho n2)
| Mod (n1,n2)-> modulus (eval rho n1,eval rho n2)
| Exp (n1,n2)-> exp (eval rho n1,eval rho n2)
| Not n-> notl (eval rho n)
| And (n1,n2)-> andl (eval rho n1,eval rho n2)
| Or (n1,n2)-> orl (eval rho n1,eval rho n2)
| Imp (n1,n2)-> implies (eval rho n1,eval rho n2)
| Equals (n1,n2)-> equals (eval rho n1,eval rho n2)
| Grthan (n1,n2)-> greater (eval rho n1,eval rho n2)
| Grteql (n1,n2)-> greateq (eval rho n1,eval rho n2)
| Lesthan (n1,n2)-> lesser (eval rho n1,eval rho n2)
| Leseql (n1,n2)-> lesseql (eval rho n1,eval rho n2)
| Proj (n1,Tup n2)-> eval rho (List.nth n2 (extract_int (eval rho n1)))
|_-> raise Unmatch;;

let rec compile e=match e with
Const n->[CONST n]
| Var x->[LOOKUP x]
| Bool b->[BOOL b]
| Tup t->[(TUP (List.map compile t))]
| Abs n->(compile n)@[ABS]
| Succ n->(compile n)@[SUCC]
| Pred n->(compile n)@[PRED]
| Plus (n1,n2)->(compile n1)@(compile n2)@[PLUS]
| Subtract (n1,n2)->(compile n1)@(compile n2)@[MINUS]
| Mult (n1,n2)->(compile n1)@(compile n2)@[MULT]
| Div (n1,n2)->(compile n1)@(compile n2)@[DIV]
| Mod (n1,n2)->(compile n1)@(compile n2)@[MOD]
| Exp (n1,n2)->(compile n1)@(compile n2)@[EXP]
| Not n->(compile n)@[NOT]
| And (n1,n2)->(compile n1)@(compile n2)@[AND]
| Or (n1,n2)->(compile n1)@(compile n2)@[OR]
| Imp (n1,n2)->(compile n1)@(compile n2)@[IMP]
| Equals (n1,n2)->(compile n1)@(compile n2)@[EQUALS]
| Grthan (n1,n2)->(compile n1)@(compile n2)@[GRTHAN]
| Grteql (n1,n2)->(compile n1)@(compile n2)@[GRTEQL]
| Lesthan (n1,n2)->(compile n1)@(compile n2)@[LESTHAN]
| Leseql (n1,n2)->(compile n1)@(compile n2)@[LESEQL]
| Proj (n1,n2)->(compile n1)@(compile n2)@[PROJ];;

let rec map f lis =match lis with
[]->[]
|x::xs -> (f ([],rho,x))::(map f xs);;

let rec execute (s,rho,c)=match (s,c) with
  (s,[])->hd s
| (s,(CONST n)::c')->execute ((Integer n)::s,rho,c')
| (s,(LOOKUP x)::c')->execute ((rho x)::s,rho,c')
| (s,(BOOL b)::c')->execute ((Boolean b)::s,rho,c')
| (s,(TUP t)::c')->execute ((Tuple (map execute t))::s,rho,c')
| ((Integer n)::s,ABS::c')->execute ((abs (Integer n))::s,rho,c')
| ((Integer n)::s,SUCC::c')->execute ((succ (Integer n))::s,rho,c')
| ((Integer n)::s,PRED::c')->execute ((pred (Integer n))::s,rho,c')
| ((Integer n2)::(Integer n1)::s',PLUS::c')->execute (add (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',MINUS::c')->execute (sub (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',MULT::c')->execute (mult (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',DIV::c')->execute (div (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',MOD::c')->execute (modulus (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',EXP::c')->execute (exp (Integer n1,Integer n2)::s',rho,c')
| ((Boolean b)::s',NOT::c')->execute ((notl (Boolean b))::s',rho,c')
| ((Boolean b2)::(Boolean b1)::s',AND::c')->execute (andl (Boolean b1,Boolean b2)::s',rho,c')
| ((Boolean b2)::(Boolean b1)::s',OR::c')->execute (orl (Boolean b1,Boolean b2)::s',rho,c')
| ((Boolean b2)::(Boolean b1)::s',IMP::c')->execute (implies (Boolean b1,Boolean b2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',EQUALS::c')->execute (equals (Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',GRTHAN::c')->execute (greater(Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',GRTEQL::c')->execute (greateq(Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',LESTHAN::c')->execute (lesser(Integer n1,Integer n2)::s',rho,c')
| ((Integer n2)::(Integer n1)::s',LESEQL::c')->execute (lesseql(Integer n1,Integer n2)::s',rho,c')
| ((Tuple t)::(Integer n1)::s',PROJ::c')->execute((List.nth t (extract_int (Integer n1)))::s',rho,c')
| _->raise EmptyStack;;



let a=Tup [Const 1;Plus(Const 1, Const 1);Div(Const 6,Const 2);Mult(Plus(Const 1,Const 1),Const 2)];;
let b=Proj (Plus(Const 1,Const 1),a);;
let c=compile b;;
execute([],rho,c);;
eval rho b;;


let d=Bool false;;
let i=Bool true;;
let j=Bool true;;
let e=Not (And(d,Or(i,Imp(d,j))));;
let f=compile e;;
execute([],rho,f);;
eval rho e;;

let g=Plus(Var "x",Mult(Mod(Const 32,Const 11),Exp(Const 2,Const 2)));;
let h=compile g;;
execute([],rho,h);;
eval rho g;;


let t1=Plus(Const 1, Const 2);;
let t2=Mult(Const 6, Const 6);;
let t3=Mult(Const 2, Const 4);;
let t4=Div(Const 6, Const 3);;
let t5=Var "iden1";;
let t6=Var "iden2";;
let t7=Abs (Const (-1));;
let t8=Proj(Const 2,Tup [Const 12;Const 121;Const 33]);;
let t9=Subtract(Proj(Const 2,Tup [Const 2;Const 5;Const 8]),Const 1);;
let t10=Mod(Proj(Const 2,Tup [Const 2;Const 5; Const 8]),Const 2);;
let t11=And(Bool true, Bool false);;
let t12=Imp(Not(Imp(Or(Bool true,Bool false),And(Bool true, Bool false))),Imp(And(Bool true, Bool false),Or(Bool true, Bool false)));;
let t13=Grteql(Const 4, Const 2);;
let t14=Leseql(Const 4, Const 2);;

let tc1=compile t1;;
let tc2=compile t2;;
let tc3=compile t3;;
let tc4=compile t4;;
let tc5=compile t5;;
let tc6=compile t6;;
let tc7=compile t7;;
let tc8=compile t8;;
let tc9=compile t9;;
let tc10=compile t10;;
let tc11=compile t11;;
let tc12=compile t12;;
let tc13=compile t13;;
let tc14=compile t14;;

execute([],rho,tc1);;
execute([],rho,tc2);;
execute([],rho,tc3);;
execute([],rho,tc4);;
execute([],rho,tc5);;
execute([],rho,tc6);;
execute([],rho,tc7);;
execute([],rho,tc8);;
execute([],rho,tc9);;
execute([],rho,tc10);;
execute([],rho,tc11);;
execute([],rho,tc12);;
execute([],rho,tc13);;
execute([],rho,tc14);;

eval rho t1;;
eval rho t2;;
eval rho t3;;
eval rho t4;;
eval rho t5;;
eval rho t6;;
eval rho t7;;
eval rho t8;;
eval rho t9;;
eval rho t10;;
eval rho t11;;
eval rho t12;;
eval rho t13;;
eval rho t14;;


eval rho (Or(Equals(Const(5),Const(5)),And(Equals(Subtract(Const(2),Const(1)),Const(1)),Mod(Proj(Const 2,Tup[Const(2);Const(5);Const(8)]),Const(2)))));
