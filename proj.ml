(* Tipi ammissibili come set *)
(* I Set possono essere di questi tipi *)
type myTypes = 
  | Tint
  | Tbool
  | Tstring
;;

(* Grammatica del linguaggio *)
type ide = string;; (* identificatore *)
type exp = 
    (* AST *)
  | Eint of int
  | Ebool of bool
  | Estring of string
  | Den of ide (* Ci permette di avere il valore dato un identificatore *)
  | Prod of exp * exp
  | Sum of exp * exp
  | Diff of exp * exp
  | Eq of exp * exp
  | Minus of exp
  | IsZero of exp
  | Or of exp * exp
  | And of exp * exp
  | Not of exp
  | Ifthenelse of exp * exp * exp
  | Let of ide * exp * exp
  | Fun of ide * exp
  | Apply of exp * exp
  | Letrec of ide * ide * exp * exp (* nomefunzione, nomeparametro, corpofunzione, corpolet *)
    (* Estensione set *)
    (* Costruttori *)
  | Empty of myTypes (* costruttore Set vuoto *)
  | Singleton of exp * myTypes (* costruttore Set composto da una espressione di tipo myTypes *)
  | Of of (myTypes * myList) 
    (* Operazioni base *)
  | Union of exp * exp
  | Intersection of exp * exp
  | Difference of exp * exp
  | Insert of exp * exp 
  | Remove of exp * exp 
  | IsEmpty of exp
  | Contains of exp * exp 
  | Subset of exp * exp 
  | MinValue of exp
  | MaxValue of exp 
    (* Operatori funzionali *)
  | For_all of exp * exp 
  | Exists of exp * exp 
  | Filter of exp * exp 
  | Map of exp * exp  
and myList = EmptyVal | Item of exp * myList
;;

(* The polymorphic environment *)
type 'v env = (string * 'v) list;;

(* Valori esprimibili ovvero il risultato della valutazione
   delle espressioni *)
type evT =
    (* Valori run-time *)
  | Int of int
  | String of string
  | Bool of bool  
  | Closure of evFun (* where ide = nome parametro formale, exp = codice funzione dichiarata, evT env = ambiente di dichiarazione *)
  | RecClosure of ide * evFun
  | Unbound 
    (* Set Extension *)
  | SetValue of (myTypes * evT list) (* lista di coppie <tipo set, valore esprimibile> *)
and evFun = ide * exp * evT env;; (* Closure *)
(* dove:
   ide = nome del parametro formale
   exp = corpo della funzione
   env = ambiente durante la dichiarazione
   Static Scoping ==> i riferimenti non locali sono 
   risolti nell'ambiente di dichiarazione della funzione. *)

(* empty_env returns an empty environment *)
let empty_env : evT env = [("", Unbound)]
(* bind adds a new binding to a pre-existing environment *)
let bind (env : evT env) (x : ide) (v : evT) = (x, v)::env
(* lookup looks for the value of the variable identified by x in the environment *)
let rec lookup (env : evT env) (x : ide) = 
  match env with
  | []                    -> Unbound
  | (a, v)::_ when a = x  -> v
  | _::e                  -> lookup e x;;

(* Type checker dinamico *)
(* L’informazione sui tipi è conosciuta solamente a tempo di esecuzione *)
(* Prende in input una stringa (sType) e un valore esprimibile e controlla 
   se i tipi sono coerenti. *)
let typecheck (sType : string) (value : evT) : bool =
  match sType with
  | "int" -> (match value with
      | Int(_) -> true
      | _ -> false)
  | "string" -> (match value with
      | String(_) -> true
      | _ -> false)
  | "bool" -> (match value with
      | Bool(_) -> true
      | _ -> false)
  | _ -> failwith("Not valid type")
;;

(* valore -> tipo validato da SetValue (appartenente a myTypes) *)
let extractType (value : evT) : myTypes =
  match value with
  | Int(_) -> Tint
  | String(_) -> Tstring
  | Bool(_) -> Tbool
  | _ -> failwith("Not valid type");;

(* typechecking dinamico sui tipi accettati da SetValue (appartenti a myTypes) *)
(* dato un un valore esprimibile e un tipo di Set, si fa il typecheck
   del valore esprimibile in base al tipo di Set. *)
let setTypeCheck (sType : myTypes) (value : evT) : bool =
  match sType with
  | Tint -> typecheck "int" value
  | Tstring -> typecheck "string" value 
  | Tbool -> typecheck "bool" value
;;

(* Operazioni di base*)
(* Valutazione eager: prima di applicare l'operatore, si valutano
   tutte le sottoespressioni *)
(* Prima di fare operazioni come la somma, si controllano i tipi degli argomenti *)
let sum x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with 
      | (Int(n), Int(m)) -> Int(n+m) (* Se non ci sono errori di tipo allora ritorna la somma *)
      | _ -> failwith("Sum Type Error"))
  else failwith("Sum Type Error")
;;

let rev lst = 
  let rec aux acc = function
    | [] -> acc
    | h::t -> aux (h::acc) t in 
  aux [] lst;; 

let prod x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
      | (Int(n), Int(m)) -> Int(n*m) (* Se non ci sono errori di tipo allora ritorna il prodotto *)
      | _ -> failwith("Product Type Error"))
  else failwith("Product Type Error")
;;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
      | (Int(n), Int(m)) -> Int(n - m) (* Se non ci sono errori di tipo allora ritorna la differenza *)
      | _ -> failwith("Difference Type Error>"))
  else failwith("Difference Type Error")
;;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
  then (match (x, y) with
      | (Int(n), Int(m)) -> Bool(n = m) (* Se non ci sono errori di tipo allora ritorna vero se le due exp sono uguali *)
      | _ -> failwith("Equal Type Error>"))
  else failwith("Equal Type Error")
;;

let minus x = if (typecheck "int" x)
  then (match x with
      | Int(n) -> Int(-n)
      | _ -> failwith("Minus Type Error"))
  else failwith("Minus Type Error")
;;

let iszero x = if (typecheck "int" x)
  then (match x with
      | Int(n) -> Bool(n = 0)
      | _ -> failwith("IsZero Type Error>"))
  else failwith("IsZero Type Error")
;;

let b_or x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x, y) with
      | (Bool(b), Bool(b1)) -> Bool(b || b1)
      | _ -> failwith("Boolean OR Type error"))
  else failwith("Boolean OR Type error")
;;

let b_and x y = if (typecheck "bool" x) && (typecheck "bool" y)
  then (match (x, y) with
      | (Bool(b), Bool(b1)) -> Bool(b && b1)
      | _ -> failwith("Boolean AND Type error"))
  else failwith("Boolean AND Type error")
;;

let b_not b = if (typecheck "bool" b)
  then (match b with
      | Bool(true)  -> Bool(false)
      | Bool(false) -> Bool(true)
      | _ -> failwith("Boolean NOT Type error"))
  else failwith("Boolean NOT Type error")
;;

let rec contains el l = match l with
  | [] -> false
  | x::xs ->
      if (x = el) then true
      else contains el xs
;;

(* Estensione delle funzioni invocate in eval *)
let set_union l1 l2 =
  let rec aux l1 l2 acc = match l1 with
    | [] -> acc@l2
    | x::xs ->
        if (contains x l2) then aux xs l2 acc 
        else aux xs l2 acc@[x]
  in aux l1 l2 []
;;
let set_insert el l = 
  if (contains el l) then l
  else 
    let rec aux el l acc = match l with
      | [] -> acc@[el]
      | x::xs -> aux el xs acc@[x]
    in aux el l []
;;

let set_remove el l = 
  if (contains el l = false) then l
  else 
    let rec aux el l acc = match l with
      | [] -> acc
      | x::xs -> 
          if (x = el) then aux el xs acc
          else aux el xs acc@[x]
    in aux el l []
;;

let rec set_subset l1 l2 = match l1 with
  | [] -> true
  | x::xs -> 
      if (contains x l2) then set_subset xs l2
      else false
;;

let set_min l = match l with
  | [] -> failwith("La lista e' vuota") 
  | x::xs -> 
      let rec aux l acc = match l with
        | [] -> acc
        | x::xs -> 
            if (x < acc) then aux xs x
            else aux xs acc
      in aux xs x
;;

let set_max l = match l with
  | [] -> failwith("La lista e' vuota") 
  | x::xs -> 
      let rec aux l acc = match l with
        | [] -> acc
        | x::xs -> 
            if (x > acc) then aux xs x
            else aux xs acc
      in aux xs x
;;

let set_intersection l1 l2 = 
  let rec aux l1 l2 acc = match l1 with
    | [] -> acc
    | x::xs -> 
        if (contains x l2) then aux xs l2 acc@[x]
        else aux xs l2 acc
  in aux l1 l2 []
;;

let set_difference l1 l2 = 
  let rec aux l1 l2 acc = match l1 with
    | [] -> acc
    | x::xs -> 
        if (contains x l2) then aux xs l2 acc
        else aux xs l2 acc@[x]
  in aux l1 l2 []
;;

(* Ciclo interprete *)
let rec eval (e: exp) (environment :evT env) : evT = match e with
  | Eint n -> Int n (* Dati primitivi *)
  | Ebool b -> Bool b
  | Estring s -> String s
  | Den i -> lookup environment i (* Applico l'ambiente per vedere se il denotabile esiste (es. Apply) *)
  | Prod(a, b) -> prod (eval a environment) (eval b environment)
  | Sum(a, b) -> sum (eval a environment) (eval b environment)
  | Diff(a, b) -> diff (eval a environment) (eval b environment)
  | Eq(a, b) -> eq (eval a environment) (eval b environment)
  | Minus a -> minus (eval a environment)
  | IsZero a -> iszero (eval a environment)
  | Or(a, b) -> b_or (eval a environment) (eval b environment)
  | And(a, b) -> b_and (eval a environment) (eval b environment)
  | Not a -> b_not (eval a environment)
    (* La valutazione del condizionale non segue una strategia eager:
       è l’operatore che richiede la valutazione dei sottoalberi,
       in base alla valutazione della guardia *)
  | Ifthenelse(a, b, c) ->
      let g = (eval a environment) in
      if (typecheck "bool" g) then
        (if g = Bool(true) then
           (eval b environment)
         else
           (eval c environment))
      else failwith ("Non boolean statement condition")
    (* Con il Let possiamo cambiare l’ambiente in punti arbitrari
       all’interno di una espressione *)
    (* Uso la semantica operazionale del Let, quindi valuto prima e2 e
       aggiungendo all'ambiente i valuto e1*)
    (* I blocchi possono essere annidati (stack dei record di attivazione)*)
  | Let(i, e1, e2) -> eval e2 (bind environment i (eval e1 environment))

    (* Funzioni anonime:
       l'espressione OCaml:
            let f x = x + 7 in f 2
       diventa:
            Let("f", Fun("x", Sum(Den("x"), Eint(7))), Apply(Den("f"),Eint(2)) )
*)
  | Fun(i, a) -> Closure(i, a, environment) (* Prende in input un ide, il corpo della funzione e un ambiente *)
    (* e ritorna una closure *)

    (* let fact = Fun("x", ( Ifthenelse(Eq(Den("x"), Eint(1)), Eint(1), Prod(Den("x"), Apply(Den("fact"), Diff(Den("x"), Eint(1)))))));;
       let recFunTest = Letrec("fact", fact, Apply(Den("fact"), Eint(4)));; *)

  | Apply(f, eArg) -> (* Rappresenta la chiamata di funzione, input: - e parametri funzione *)
      let fClosure = (eval f environment) in (* Valuto il nome della funzione nell'ambiente e mi ritorna il tipo della funzione dichiarata *)
      (match fClosure with  
       | Closure(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg (eval eArg environment))
       | RecClosure(g, (arg, fBody, fDecEnv)) ->
           let aVal = (eval eArg environment) in (* parametro attuale valutato *)
           let rEnv = (bind fDecEnv g fClosure) in (* ambiente di dichiarazione esteso con associazione tra nome e chiusura ricorsiva *)
           let aEnv = (bind rEnv arg aVal) in (* estendo l'ambiente di sopra con la valutazione del parametro attuale *)
           eval fBody aEnv
       | _ -> failwith("Type is not a closure"))

  | Letrec(f, param, funDef, lBody) ->
      (match funDef with
       | Fun(i, fBody) ->
           let r1 = (bind environment f (RecClosure(f, (i, fBody, environment))))
           in eval lBody r1
       | _ -> failwith("Type is not a function")) 


  | Empty(t) -> SetValue(t, [])
    
  | Singleton(exp, t) ->
      let evaluated = (eval exp environment) in
      if (setTypeCheck t evaluated) then
        SetValue(t, evaluated::[])
      else
        failwith("Inconsistent Types")    
       
  | Of(t, l) -> 
      let rec evaluateList (slist : myList) (sType : myTypes) (r : evT env) : evT list = match slist with
        | EmptyVal -> []
        | Item(expr, xs) ->
            let evaluated = (eval expr r) in
                (* Controllo la correttezza e la coerenza dei tipi *)
            if (setTypeCheck sType evaluated) then
              evaluated::(evaluateList xs sType r)
            else
              failwith("Inconsistent type") in 
      let ll = evaluateList l t environment in 
      let rec duplicates l1 = match l1 with
        | [] -> true
        | x::xs -> 
            if (contains x xs) then false
            else duplicates xs
      in 
                        (* Controllo che non siano presenti duplicati *)
      if (duplicates ll) then SetValue(t, ll)
      else failwith("Duplicates in Set")
    
  | Union(s1, s2) -> (match (eval s1 environment, eval s2 environment) with
      | (SetValue(t1, l1), SetValue(t2, l2)) -> 
          if (t1 = t2) then SetValue(t1, set_union l1 l2) 
          else failwith("Inconsistent Types")
      | _ -> failwith("Type is not a set"))
    
  | Intersection(s1, s2) -> (match (eval s1 environment, eval s2 environment) with
      | (SetValue(t1, l1), SetValue(t2, l2)) -> 
          if (t1 = t2) then SetValue(t1, set_intersection l1 l2) 
          else failwith("Inconsistent Types")
      | _ -> failwith("Type is not a set"))

  | Difference(s1, s2) -> (match (eval s1 environment, eval s2 environment) with
      | (SetValue(t1, l1), SetValue(t2, l2)) -> 
          if (t1 = t2) then SetValue(t1, set_difference l1 l2)
          else failwith("Inconsistent Types")
      | _ -> failwith("Type is not a set"))
    
  | Insert(el, s) -> (match eval s environment with
      | SetValue(t, l) -> 
          if (setTypeCheck t (eval el environment)) then SetValue(t, set_insert (eval el environment) l) 
          else failwith("Inconsistent Types")
      | _ -> failwith("Type is not a set"))

  | Remove(el, s) -> (match eval s environment with
      | SetValue(t, l) -> 
          if (setTypeCheck t (eval el environment)) then SetValue(t, set_remove (eval el environment) l) 
          else failwith("Inconsistent Types")
      | _ -> failwith("Type is not a set"))
    
  | IsEmpty(s) -> (match eval s environment with
      | SetValue(t, l) -> 
          if (l = []) then Bool(true)
          else Bool(false)
      | _ -> failwith("Type is not a set"))
    
  | Contains(el, s) -> (match eval s environment with
      | SetValue(t, l) -> 
          if (setTypeCheck t (eval el environment) && contains (eval el environment) l) then Bool(true) 
          else Bool(false)
      | _ -> failwith("Type is not a set"))
    
  | Subset(s1, s2) -> (match (eval s1 environment, eval s2 environment) with
      | (SetValue(t1, l1), SetValue(t2, l2)) -> 
          if (t1 = t2) then Bool(set_subset l1 l2)
          else b_not (Bool(set_subset l1 l2))
      | _ -> failwith("Type is not a set"))
    
  | MinValue(s) -> (match eval s environment with
      | SetValue(t, l) -> (match l with
          | [] -> failwith("Empty Set")
          | x::xs -> if (typecheck "int" x) then set_min l
          else failwith("Non comparable type"))
      | _ -> failwith("Type is not a set"))

  | MaxValue(s) -> (match eval s environment with
      | SetValue(t, l) -> (match l with
          | [] -> failwith("Empty Set")
          | x::xs -> if (typecheck "int" x) then set_max l
          else failwith("Non comparable type"))

      | _ -> failwith("Type is not a set"))

      (* let setForAll = For_all(Fun("y", IsZero(Den "y")), st3);;
        eval setForAll empty_env;; *)

  | For_all(f, s) -> 
    let s1 = eval s environment in (* String("test") *)
    let f1 = eval f environment in (* Closure("x", IsZero(Den "x"), env) *)
      (match (f1, s1) with

       | (Closure(id, fBody, env), SetValue(setType, lst)) -> 
           let rec apply (f : exp) (list : evT list) (environment : evT env) : evT = (match list with
               | [] -> Bool(true)
               | x::xs ->
                  let decEnv = bind env id x in
                  let value = eval fBody decEnv in
                  (* Controllo dei tipi *)
                   if (extractType value = Tbool) then 
                    if (value = Bool(true)) then apply f xs environment
                    else Bool(false)
                  else Bool(false)) (* Il tipo di ritorno della funzione non è compatibile con l'elemento del set *)
           
           in apply f lst environment

        | (RecClosure(fName, (id, fBody, env)), SetValue(setType, lst)) -> 
          let rec apply (f : exp) (list : evT list) (environment : evT env) : evT = (match list with
          | [] -> Bool(true)
          | x::xs ->
             let envEval = bind env id x in
              let finalEval = bind envEval fName f1 in
             let value = eval fBody finalEval in
              (* Controllo dei tipi *)
             if (extractType value = Tbool) then
              if (value = Bool(true)) then apply f xs environment
              else Bool(false)
            else Bool(false)) (* Il tipo di ritorno della funzione non è compatibile con l'elemento del set*)
     
      in apply f lst environment

       | _ -> failwith("Type error in parameters"))
    
  | Exists(f, s) -> 
    let s1 = eval s environment in
    let f1 = eval f environment in
      (match (f1, s1) with

       | (Closure(id, fBody, env), SetValue(setType, lst)) -> 
           let rec apply (f : exp) (list : evT list) (environment : evT env) : evT = (match list with
               | [] -> Bool(false)
               | x::xs ->
                  let decEnv = bind env id x in
                  let value = eval fBody decEnv in 
                  (* Controllo dei tipi *)
                  if (extractType value = Tbool) then 
                   if (value = Bool(true)) then Bool(true)
                   else apply f xs environment
                  else Bool(false))

           in apply f lst environment

        | (RecClosure(fName, (id, fBody, env)), SetValue(setType, lst)) -> 
          let rec apply (f : exp) (list : evT list) (environment : evT env) : evT = (match list with
          | [] -> Bool(false)
          | x::xs ->
             let envEval = bind env id x in
              let finalEval = bind envEval fName f1 in
             let value = eval fBody finalEval in
            (* Controllo dei tipi *)
             if (extractType value = Tbool) then
              if (value = Bool(true)) then Bool(true)
              else apply f xs environment
            else Bool(false))
            
      in apply f lst environment

       | _ -> failwith("Type error in parameters"))
    
  | Filter(f, s) -> 
    let s1 = eval s environment in
    let f1 = eval f environment in
      (match (f1, s1) with

       | (Closure(id, fBody, env), SetValue(setType, lst)) -> 
           let rec apply (f : exp) (list : evT list) (environment : evT env) (acc: evT list) : evT list = (match list with
               | [] -> acc
               | x::xs ->
                  let decEnv = bind env id x in
                  let value = eval fBody decEnv in
                  (* Controllo dei tipi *)
                  if (extractType value = Tbool) then
                    if (value = Bool(true)) then apply f xs environment (x::acc)
                    else apply f xs environment acc
                  else failwith("TYPE ERROR"))

           in SetValue(setType, apply f lst environment [])

        | (RecClosure(fName, (id, fBody, env)), SetValue(setType, lst)) -> 
          let rec apply (f : exp) (list : evT list) (environment : evT env) (acc: evT list) : evT list = (match list with
          | [] -> acc
          | x::xs ->
             let envEval = bind env id x in
              let finalEval = bind envEval fName f1 in
             let value = eval fBody finalEval in
              (* Controllo dei tipi *)
             if (extractType value = Tbool) then
              if (value = Bool(true)) then apply f xs environment (x::acc)
              else apply f xs environment acc
             else failwith("TYPE ERROR"))

      in SetValue(setType, apply f lst environment [])

       | _ -> failwith("Type error in parameters"))

  | Map(f, s) -> 
    let s1 = eval s environment in
    let f1 = eval f environment in
      (match (f1, s1) with

       | (Closure(id, fBody, env), SetValue(setType, lst)) -> 
           let rec apply (f : exp) (list : evT list) (environment : evT env) (acc: evT list) : evT list = (match list with
               | [] -> acc
               | x::xs ->
                    let decEnv = bind env id x in
                    let value = eval fBody decEnv in
                      (* Controllo dei tipi *)
                      if (extractType value = setType) then
                        apply f xs environment (value::acc)
                      else failwith("TYPE ERROR"))

           in let gotSet = (apply f lst environment []) in

           let rec searchForDuplicates genericSet =
            (match genericSet with
            | [] -> false
            | x::xs -> if (contains x xs) then true
                    else searchForDuplicates xs )
          in let areDuplicates = searchForDuplicates gotSet in
              if (areDuplicates = true) then failwith("Duplicates in set")
              else SetValue(setType, rev gotSet)

        | (RecClosure(fName, (id, fBody, env)), SetValue(setType, lst)) -> 
          let rec apply (f : exp) (list : evT list) (environment : evT env) (acc: evT list) : evT list = (match list with
          | [] -> acc
          | x::xs ->
            (*if (extractType x = setType) then*) 
             let envEval = bind env id x in
              let finalEval = bind envEval fName f1 in
             let value = eval fBody finalEval in
              (* Controllo dei tipi *)
              if (extractType value = setType) then
                apply f xs environment (value::acc)
              else failwith("TYPE ERROR"))

            in let gotSet = (apply f lst environment []) in
 
            let rec searchForDuplicates genericSet =
             (match genericSet with
             | [] -> true
             | x::xs -> if (contains x xs) then false
                     else searchForDuplicates xs )
           in let areDuplicates = searchForDuplicates gotSet in
               if (areDuplicates = true) then failwith("Duplicates in set")
               else SetValue(setType, rev gotSet)

       | _ -> failwith("Type error in parameters"))

(* ------------ TESTING PART ------------*)

(* CONSTRUCTORS *)
(* Empty constructor *)
let emptySet = Empty(Tint);;
eval emptySet empty_env;;
(* # eval emptySet empty_env;;
- : evT = SetValue (Tint, []). *)

(* Singleton constructor *)
let singletonSet = Singleton(Prod(Eint 5, Eint 4), Tint);;
eval singletonSet empty_env;;
(* # eval singletonSet empty_env;;
- : evT = SetValue (Tint, [Int 20]). *)

(* Of constructor *)
let s1 = Of(
    (
      Tint, (
        Item( Eint 9,
              Item( Eint 2,
                    Item( Eint 3,
                          Item( Eint 1,
                                EmptyVal))))
      )
    )
  );;
eval s1 empty_env;;

(* # eval s1 empty_env;;
- : evT = SetValue (Tint, [Int 9; Int 2; Int 3; Int 1]). *)

let s2 = Of(
    (
      Tint, (
        Item( Eint 4,
              Item( Eint 2,
                    Item( Eint 1,
                          Item( Eint 0,
                                EmptyVal))))
      )
    )
  );;
eval s2 empty_env;;

(* # eval s2 empty_env;;
- : evT = SetValue (Tint, [Int 4; Int 2; Int 1; Int 0]). *)

(* Non homogeneous set are not allowed *)
let nonHomogeneousSet = Of (
    (
      Tint, (
        Item( Eint 3,
              Item( Estring "hi",
                    EmptyVal))
      )
    )
  );;
(* # eval nonHomogeneousSet empty_env;;
Exception: Failure "Non homogeneous set". *)

(* Duplicates are not allowed *)
let duplicatesSet = Of(
    (
      Tint, (
        Item( Eint 1,
              Item( Eint 2,
                    Item( Eint 2,
                          Item( Eint 1,
                                EmptyVal))))
      )
    )
  );;
(* # eval duplicatesSet empty_env;;
Exception: Failure "Duplicates in Set". *)

(* Type error in Singleton*)
let setError1 = Singleton(Sum(Eint 5, Eint 5), Tstring);;
(* # eval setError1 empty_env;; 
Exception: Failure "Inconsistent Types". *)

(* Type error in Sum *)
let setError2 = Singleton(Sum(Estring "e", Eint 1), Tint);;
(* eval setError2 empty_env;;
Exception: Failure "Sum Type Error". *)

(* PRIMITIVE SET OPERATIONS *)
let setUnion = Union(s1, s2);;
eval setUnion empty_env;;
(* # eval setUnion empty_env;;
- : evT = SetValue (Tint, [Int 4; Int 2; Int 1; Int 0; Int 3; Int 9]). *)

let setIntersection = Intersection(s1, s2);;
eval setIntersection empty_env;;
(* # eval setIntersection empty_env;;
- : evT = SetValue (Tint, [Int 1; Int 2]). *)

let setDifference = Difference(s1, s2);;
eval setDifference empty_env;;
(* # eval setDifference empty_env;;
- : evT = SetValue (Tint, [Int 3; Int 9]). *)

(* FUNCTIONS *)
let st1 = Of(
    (
      Tint, 
      Item( Eint 5, 
            Item( Eint 1, 
                  Item( Eint 3, 
                        EmptyVal)))
    )
  );;

let st2 = Of(
    (
      Tint, 
      Item( Eint 1, 
            Item( Eint 0, 
                  Item( Eint 3, EmptyVal)))
    )
  );;

let st3 = Of(
    (
      Tint, 
      Item( Eint 1, 
            Item( Eint 0, EmptyVal))
    )
  );;

let st4 = Of(
    (
      Tint, 
      Item( Eint 1, 
            Item( Eint 0, EmptyVal))
    )
  );;
eval st4 empty_env;;

let singletonSetZero = Singleton(Eint 0, Tint);;

(* INSERIMENTO *)
let setInsOp = Insert(Eint 5, st4);;
eval setInsOp empty_env;;
(* - : evT = SetValue(Tint, [Int 5; Int 0; Int 1])*)

let setInsOpErr = Insert(Estring "a", st4);;
eval setInsOpErr empty_env;;
(* - : Failure "Inconsistent Types"*)

(* RIMOZIONE *)
let setRemOp = Remove(Eint 5, st4);;
eval setRemOp empty_env;;
(* - : evT = SetValue(Tint, [Int 1; Int 0])*)

(* ISEMPTY *)
let isEmptyOp = IsEmpty(Empty(Tint));;
eval isEmptyOp empty_env;;
(* - : evT = Bool true *)

(* CONTAINS *)
let containsOp = Contains(Eint 1, st4);;
eval containsOp empty_env;;
(* - : evT = Bool true *)

(* SUBSET *)
let setSubsetOp = Subset(
    Of((Tint, ( Item( Eint 1, Item( Eint 2, EmptyVal))))),
    Of((Tint, ( Item( Eint 1, Item( Eint 2, Item( Eint 3, EmptyVal))))))
);;
eval setSubsetOp empty_env;;

(* MIN,MAX *)
let setMinValOp = MinValue(st4);;
eval setMinValOp empty_env;;
(* - : evT = Int 0 *)

(* Errore tipo non comparabile *)
let setMinValueOp = MinValue(Of((Tstring, ( Item( Estring "1", Item( Estring "2", EmptyVal))))));;
(* eval setMinValueOp empty_env;; *)

let setMaxValueOp = MaxValue(Empty(Tint));;
eval setMaxValueOp empty_env;;
(* - : Failure "Empty Set"*)

let setMaxValueOp2 = MaxValue(st4);;
eval setMaxValueOp2 empty_env;;
(* - : evT = Int 1 *)

(* FORALL, EXISTS, FILTER, MAP *)
(* Errore di tipo nei parametri *)
let setForAllErr = For_all(Fun("x", IsZero(Den "x")), Estring "test");;
(* eval setForAllErr myEnv;; *)

let setForAll = For_all(Fun("y", IsZero(Den "y")), singletonSetZero);;
eval setForAll empty_env;;

let existSetTest = Exists(Fun("y", IsZero(Den "y")), st1);;
eval existSetTest empty_env;;

let setFilter = Filter(Fun("x", IsZero(Den "x")), st2);;
eval setFilter empty_env;;

let testFilterErr = Filter(Fun("y", IsZero(Den "y")), st2);;
eval testFilterErr empty_env;;
(* Exception: Failure "TYPE ERROR". *)

let setMap = Map(Fun("x", Sum(Den "x", Eint 1)), st1);;
eval setMap empty_env;;
(* # eval setMap empty_env;;
- : evT = SetValue (Tint, [Int 6; Int 2; Int 4]). *)

let setMapErr = Map(Fun("x", IsZero(Den "x")), st2);;
eval setMapErr empty_env;; 
(* Exception: Failure "TYPE ERROR". *)

(* FUNCTION USING RECURSION*)
let fact = Fun("x", ( Ifthenelse(Eq(Den("x"), Eint(1)), Eint(1), Prod(Den("x"), Apply(Den("fact"), Diff(Den("x"), Eint(1)))))));;
(* nomefunc, *)
let recFunTest = Letrec("fact", "n", fact, Apply(Den("fact"), Eint(4)));;
eval recFunTest empty_env;;
(* # eval recFunTest empty_env;;
- : evT = Int 24. *)
