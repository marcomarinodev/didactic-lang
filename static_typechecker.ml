(* Grammatica del linguaggio *)
type ide = string;;

type myTypes = 
    | Tint
    | Tbool
    | Tstring
    | Tset of myTypes
    | Tfun of myTypes * myTypes
    | Unbound;; 

type exp = 
    (* Abstract Syntax Tree *)
    | Eint of int
    | Ebool of bool
    | Estring of string
    | Den of ide
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
    | Fun of ide * myTypes * exp
    | Apply of exp * exp
    (* nome funzione, nome parametro, tipo funzione (tipo dominio, tipo codominio), corpo funzione, corpo let *)
    | Letrec of ide * ide * myTypes * exp * exp
    (* Estensione set *)
    | Empty of myTypes
    | Singleton of exp * myTypes 
    | Of of (myTypes * myList) 
    (* Operazioni base *)
    | Union of exp * exp 
    | Intersection of exp * exp 
    | Difference of exp * exp (* ESet, ESet *)
    | Insert of exp * exp (* value, ESet *)
    | Remove of exp * exp (* value, ESet *)
    | IsEmpty of exp (* ESet *)
    | Contains of exp * exp (* value, ESet *)
    | Subset of exp * exp (* ESet, ESet *)
    | MinValue of exp (* ESet *)
    | MaxValue of exp (* ESet *)
    (* Operatori funzionali *)
    | For_all of exp * exp (* predicato, ESet *)
    | Exists of exp * exp (* predicato, ESet *)
    | Filter of exp * exp (* predicato, ESet *)
    | Map of exp * exp  (* predicato, ESet *)
and myList = EmptyVal | Item of exp * myList
;;

(* The polymorphic environment *)
type 'v env = (string * 'v) list;;

(* empty_env returns an empty environment *)
let empty_env = [("", Unbound)]
(* bind adds a new binding to a pre-existing environment *)
let bind (env : myTypes env) (x : ide) (v : myTypes) = (x, v)::env
(* lookup looks for the value of the variable identified by x in the environment *)
let rec lookup (env : myTypes env) (x : ide) = 
    match env with
    | []                    -> Unbound
    | (a, v)::_ when a = x  -> v
    | _::e                  -> lookup e x;;

let setTypeCheck (t: myTypes) =
    match t with
    | Tint -> true
    | Tstring -> true
    | Tbool -> true
    | _ -> false;;

let rec teval (e : exp) (environment : myTypes env) = 
    match e with
    | Eint(_) -> Tint
    | Ebool(_) -> Tbool
    | Estring(str) -> Tstring
    | Den(identifier) -> 
        let y = lookup environment identifier in
            if (y = Unbound)
                then failwith ("This is an unbound identifier")
            else y
    | Prod(e1, e2) -> 
        (match ((teval e1 environment), (teval e2 environment)) with
            | (Tint, Tint) -> Tint
            | _ -> failwith("Type error in Prod")) 
    | Sum(e1, e2) -> 
        (match ((teval e1 environment), (teval e2 environment)) with
        | (Tint, Tint) -> Tint
        | _ -> failwith("Type error in Sum"))
    | Diff(e1, e2) -> 
        (match ((teval e1 environment), (teval e2 environment)) with
        | (Tint, Tint) -> Tint
        | _ -> failwith("Type error in Diff"))  
    | Eq(e1,e2) ->
        let y1 = teval e1 environment in
        let y2 = teval e2 environment in
            if (y1 = y2)
                then Tbool
                else failwith("Comparison is not possible due to inconsistent type")
    | Minus(e1) ->
        let y1 = teval e1 environment in
            if y1 = Tint
                then Tint
                else failwith("You cannot change the sign of something that isn't an integer")
    | IsZero(e1) ->
        let y1 = teval e1 environment in
            if y1 = Tint
                then Tint
                else failwith("A non integer cannot be zero")
    | Or(e1,e2) -> 
        (match ((teval e1 environment), (teval e2 environment)) with
        | (Tbool, Tbool) -> Tbool
        | _ -> failwith("Type error in Or (Not boolean)"))
    | And(e1,e2) -> 
        (match ((teval e1 environment), (teval e2 environment)) with
        | (Tbool, Tbool) -> Tbool
        | _ -> failwith("Type error in And (Not boolean)"))
    | Not(e1) ->
        let y1 = teval e1 environment in
            if y1 = Tbool
                then Tbool
                else failwith("Expression is not a boolean")
           (* ----------- *)     
    | Ifthenelse(cond, branch1, branch2) ->
        let condType = teval cond environment in
        (match condType with
            | Tbool ->
                (match ((teval branch1 environment), (teval branch2 environment)) with
                | (Tint, Tint) -> Tint
                | (Tbool, Tbool) -> Tbool
                | (Tstring, Tstring) -> Tstring
                | (Tset(t1), Tset(t2)) -> 
                    if (t1 = t2) then Tset(t1)
                    else failwith("Different types in branches")
                | (Tfun(t1,t2), Tfun(t3,t4)) ->
                    if ((t1 = t3) && (t2=t4)) then Tfun(t1,t2)
                    else failwith("Different types in branches")
                | (_,_) -> failwith("Different types in branches")
            | _ -> failwith("Condition is not boolean")
        ))

    | Let(identifier,e1,e2) ->
        let t = teval e1 environment in
            teval e2 (bind environment identifier t)


    | Fun(identifier, paramType, e1) -> 
        let tenv1 = bind environment identifier paramType in
            let t2 = teval e1 tenv1 in Tfun(paramType, t2)
    
    | Apply(e1, e2) ->
        let f = teval e1 environment in
        (match f with
        | Tfun(paramType,retType) -> 
            if ((teval e2 environment) = paramType)
                then retType
                else failwith("Parameter type is not what was expected")
        | _ -> failwith("Wrong Type"))

    | Letrec(funName, paramName, funType, funBody, letBody) ->
        (match funType with
        | Tfun(inType, outType) ->
            let tempExtendedEnv = bind environment paramName inType in
                let extendedEnv = bind tempExtendedEnv funName funType in
                    if ((teval funBody extendedEnv) = outType)
                        then teval letBody extendedEnv
                        else failwith("Wrong output type") 
        | _ -> failwith("The function we're trying to call is not a function"))

    | Empty(setType) ->
        if ((setTypeCheck setType) = true)
            then Tset(setType)
            else failwith("Not a Set valid type") 
    
    | Singleton(e1, setType) ->
        if ((setTypeCheck setType) = true)
            then if ((teval e1 environment) = setType)
                    then Tset(setType)
                    else failwith("Expression type is different from Set type")
            else failwith("Set type error")
            
    (* Sapendo che un set è composto da:
    Of((Tint, Item(Eint 1, Item(Eint 2, EmptyVal))))
    ogni volta controllo che la x in Item(x,xs) sia 
    dello stesso tipo di setType. *)
    | Of(setType, e1) ->
        if ((setTypeCheck setType) = true)
            then let rec expressionValuation (set) =
                (match set with
                | EmptyVal -> Tset(setType)
                | Item(x,xs) -> 
                    if ((teval x environment) = setType)
                        then expressionValuation xs
                        else failwith("Inconsistent type in set"))
                in expressionValuation e1
            else failwith("This is not a set type")

    | Union(s1, s2) ->
        let set1 = teval s1 environment in
            let set2 = teval s2 environment in
            (match (set1, set2) with
                |(Tset(setType1), Tset(setType2)) ->
                    if(setType1 = setType2)
                        then Tset(setType1)
                        else failwith ("Different set type")
                |(_, _) -> failwith ("Parameters must be set"))

    | Intersection(s1, s2) ->
        let set1 = teval s1 environment in
            let set2 = teval s2 environment in
            (match (set1, set2) with
            |(Tset(setType1), Tset(setType2)) ->
                if(setType1 = setType2)
                    then Tset(setType1)
                    else failwith ("Different set type")
            |(_, _) -> failwith ("Parameters must be set"))

    | Difference(s1, s2) ->
        let set1 = teval s1 environment in
            let set2 = teval s2 environment in
            (match (set1, set2) with
            |(Tset(setType1), Tset(setType2)) ->
                if(setType1 = setType2)
                    then Tset(setType1)
                    else failwith ("Different set type")
            |(_, _) -> failwith ("Parameters must be set"))
    
    | Insert (s1, elem)->
        let set1 = teval s1 environment in
        (match set1 with
            |Tset (setType) ->
                let elemType = teval elem environment in
                    if(elemType = setType)
                        then Tset(setType)
                        else failwith ("You cannot add a value that has different type from set's one")
            |_ -> failwith ("Set Parameter must be set"))

    | Remove (s1, elem) ->
        let set1 = teval s1 environment in
        (match set1 with
            |Tset (setType) ->
                let elemType = teval elem environment in
                    if(elemType = setType)
                        then Tset(setType)
                        else failwith ("You cannot remove a value that has different type from set's one")
            |_ -> failwith ("Set Parameter must be a set"))

    | IsEmpty (set) ->
        let set1 = teval set environment in 
        (match set1 with
        | Tset(setType) -> Tbool
        | _ -> failwith("Parameter must be a set"))

    | Contains (set, elem) ->
        let set1 = teval set environment in 
        (match set1 with
        | Tset(setType) -> 
            let elemType = teval elem environment in 
                if (elemType = setType)
                    then Tbool
                    else failwith("elem type must be the same as the set type") 
        | _ -> failwith("Set Parameter must be a set"))

    | Subset (s1, s2) -> 
        let set1 = teval s1 environment in 
            let set2 = teval s2 environment in
            (match (set1, set2) with
            | (Tset(setType1), Tset(setType2)) -> 
                if (setType1 = setType2)
                    then Tbool
                    else failwith("Mismatching set types")
            | (_,_) -> failwith(""))

    | MinValue(s1) -> 
        let set1 = teval s1 environment in
        (match set1 with
        |Tset(setType) -> setType
        |_ -> failwith ("Parameter must be a set"))
        
    | MaxValue(s1) -> 
        let set1 = teval s1 environment in
        (match set1 with
        |Tset(set_type) -> set_type
        |_ -> failwith ("Parameter must be a set"))

    (* Set extension *)

    | For_all(f, s1) ->
        let predicateFun = teval  f environment in
            let set1 = teval s1 environment in 
            (match set1 with
            | Tset(setType) ->
                (match predicateFun with
                | Tfun(inputType, Tbool) ->
                    if (inputType = setType)
                        then Tbool
                        else failwith("Input type must be the same of the set type")
                | _ -> failwith("Function Parameter must be a fun "))
            | _-> failwith("Set Parameter must be a set"))
    
    | Exists(f, s1) ->
        let predicateFun = teval f environment in
            let set1 = teval s1 environment in
            (match set1 with
            |Tset(setType) ->
                (match predicateFun with
                |Tfun(inputType, Tbool) ->
                    if(inputType = setType)
                    then Tbool
                    else failwith ("Input type must be the same of set's one")
                |_ -> failwith("First argument must be a predicate"))
            |_ -> failwith("Second argument must be a set"))

    | Filter(f, s1) ->
        let predicateFun = teval f environment in
            let set1 = teval s1 environment in 
            (match set1 with
            | Tset(setType) ->
                (match predicateFun with
                | Tfun(inputType, Tbool) ->
                    if (inputType = setType)
                        then Tset(setType)
                        else failwith("Input type must be the same of set's one")
                | _ -> failwith("First argument must be a predicate"))
            | _ -> failwith("Second argument must be a set")) 

    | Map(func, s1) ->
        let funToApply = teval func environment in
            let set1 = teval s1 environment in
            (match set1 with
                |Tset(setType) ->
                    (match funToApply with
                        |Tfun(inputType, outputType) ->
                            if((inputType = setType) && (outputType = setType))
                            then Tset(outputType)
                            else failwith ("Funtion input/output type must be the seme of the set's one")
                        |_ -> failwith ("First argument must be a function"))
                |_ -> failwith ("Second argument must be a set"))

    (* TESTS *)

let st1 = Of(
    (
        Tint, 
            Item( Eint 5, 
            Item( Eint 1, Item(Eint 3, EmptyVal)))
    )
);;

let st4 = Of(
    (
        Tint, 
            Item( Eint 1, 
            Item( Eint 0, EmptyVal))
            )
);;
teval st4 empty_env;;
(* - : myTypes = Tset Tint *)

let setMap = Map(Fun("x", Tint, Sum(Den "x", Eint 1)), st1);;
teval setMap empty_env;;
    




        