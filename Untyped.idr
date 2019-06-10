import Data.Vect
%default total
data Info = String

data Term = TmVar Info Nat Nat 
          | TmAbs Info String Term
          | TmApp Info Term Term
%name Term t, t1, t2, t3

data Binding = NameBind

Context : Nat -> Type
Context k = Vect k (String, Binding)
%name Context context, context1, context2, context3

data Command = Eval Info Term
             | Bind Info String Binding

Show Binding where
  show NameBind = ""

emptyContext : Context 0
emptyContext = []

contextLength : Context n -> Nat
contextLength x {n} = n

addBinding : Context n -> String -> Binding -> Context (S n)
addBinding context name binding = (name, binding) :: context

addName : Context n -> String -> Context (S n)
addName context name = addBinding context name NameBind


isNameBound : Context n -> String -> Bool
isNameBound context name = case context of
                                [] => False
                                ((bound_name, _) :: xs) =>
                                                   if bound_name == name
                                                      then True
                                                      else isNameBound xs name

pickFreshName : (context : Context n) ->
                (name : String) ->
                {auto prf : Elem (name, _) context} ->
                Context (S n)
pickFreshName context name = (name ++ "'", NameBind) :: context

contextIndex : (a : Nat) -> {auto prf : LT 0 a} -> Nat
contextIndex (S a) {prf = (LTESucc x)} = a

indexToName : (context : Context n) -> Fin n -> String
indexToName ((name, _) :: xs) FZ = name
indexToName (x :: xs) (FS k) = indexToName xs k

nameToIndex : (context : Context n) ->
              (name : String) ->
              {auto prf : Elem (name, _) context} ->
              Nat
nameToIndex ((name, b) :: _) name {prf = Here} = 0
nameToIndex (_ :: xs) name {prf = (There later)} = 1 + nameToIndex xs name

getBinding  : (context : Context n) -> Fin n -> Binding
getBinding ((_, b) :: _) FZ = b
getBinding (_ :: xs) (FS k) = getBinding xs k

termMap : (f : (modifier : Nat) -> (cutoff : Nat) -> (t : Term) -> Term) ->
          (modifier : Nat) ->
          (cutoff : Nat) ->
          (t : Term) -> Term
termMap f modifier cutoff term = f modifier cutoff term
termMap f modifier cutoff (TmAbs fileInfo nameHint term) 
  = TmAbs fileInfo nameHint (termMap f modifier (cutoff + 1) term)
termMap f modifier cutoff (TmApp fileInfo term1 term2) 
  = TmApp fileInfo 
          (termMap f modifier cutoff term1)
          (termMap f modifier cutoff term2)

shiftAbove : (modifier : Nat) -> (cutoff : Nat) -> Term -> Term
shiftAbove modifier cutoff t = termMap shiftAboveHelper modifier cutoff t where
  shiftAboveHelper : (modifier : Nat) -> (cutoff : Nat) -> (t : Term) -> Term
  shiftAboveHelper modifier cutoff (TmVar fileInfo index check) 
    = if index >= cutoff
        then TmVar fileInfo 
                    (index + modifier) 
                    (check + modifier)
        else TmVar fileInfo index (check + modifier)
  shiftAboveHelper _ _ t = t

shift : (modifier : Nat) -> Term -> Term
shift modifier t = shiftAbove modifier 1 t 

termSubstitution : (sub_index : Nat) -> (s : Term) -> (t: Term) -> Term 
termSubstitution sub_index s t = substitutionHelper sub_index 0 t where
  substitutionHelper : (sub_index : Nat) ->
                       (cutoff : Nat) ->
                       (t : Term) ->
                       Term
  substitutionHelper sub_index cutoff (TmVar fileInfo index check)
    = if index == sub_index + cutoff
         then shift cutoff (TmVar fileInfo index check)
         else TmVar fileInfo index check
  substitutionHelper _ _ t= t

substitute : (s : Term) -> (t : Term) -> Term
substitute s t = shift 0 (termSubstitution 0 (shift 1 s) t)

checkContextLength : (t : Term) -> (context : Context n) -> Bool
checkContextLength (TmVar _ _ check) _ {n} = check == n
checkContextLength  _ _ = False


getNameFromIndex : Context n -> Nat -> Either String String
getNameFromIndex context Z {n} = Left ("Error: bad index 0/" ++ (show n) ++
                                      " in " ++ (show context))
getNameFromIndex context (S k) {n} 
  = let fin = (natToFin (contextIndex (S k)) n) in
        (case fin of
              Nothing => Left ("Error: " ++ (show (S k)) ++ "/" ++ (show n) ++
                        " in " ++ (show context))
              (Just idx) => Right (show (indexToName context idx)))

termInfo : Term -> Info
termInfo (TmVar fileInfo _ _) = fileInfo
termInfo (TmAbs fileInfo _ _) = fileInfo
termInfo (TmApp fileInfo _ _) = fileInfo

printTerm : Term -> Context n -> String
printTerm (TmVar _ index check) context {n} 
  = case (compare check n) of
         GT => ("Error: bad check " ++ (show check) ++ "/" ++ (show n) ++
              " in " ++ (show context))
         _ =>  (case getNameFromIndex context index of
                     (Left err) => err 
                     (Right res) => res)
printTerm (TmAbs _ nameHint t) context = "lambda" ++ nameHint ++ ".(\n\t" ++
                                         (printTerm t context) ++ ")"
printTerm (TmApp _ t1 t2) context = (printTerm t1 context) ++ " " ++ 
                                    (printTerm t2 context)
