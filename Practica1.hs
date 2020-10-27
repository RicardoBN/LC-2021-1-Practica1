{-
- Lógica computacional 2021-1
- Profesor: Miguel Carrillo Barajas
- Aqudante: Carlos Naranjo Robledo
- Práctica 1
- Integrantes: Ricardo Bernabé Nicolás 
-}

module LP where

--Ejercicio 1

x = "soq una cadena" --Variable como cadena
y = 10               --Variable como entero
n = fact 5           --Variable como evalucación recursiva

--Ejercicio 2

z = suma1 y          -- Definicion de valuaciones como funciones
l1 =  [(p,q) | p <- [1,2,3], q <- [4,5]] -- Variable como Lista


suma1 :: Int -> Int   
suma1 p = p+1


fact :: Int -> Int 
fact 0 = 1 
fact n = n * fact ( n - 1 ) 


--------------------------------------------------------------------
type Variable= String
data PL = Bot | Top | Var Variable  | Imp PL PL 
        | Dis PL PL | Con PL PL | Neg PL | Nand PL PL| Nor PL PL


instance Show PL where
   show (Var x) = x
   show (Neg p) = "¬"++ show p
   show (Con p q)    = "(" ++ show p ++ " ^ " ++ show q ++ ")"    
   show (Dis p q)    = "(" ++ show p ++ " V " ++ show q ++ ")"
   show (Imp p q)    = "(" ++ show p ++ " -> " ++ show q ++ ")"



-- Ejercicio 3 

vars :: PL -> [Variable]
vars (Var p) = [p]
vars (Imp p q) = (vars p) ++ (vars q)
vars (Con p q) = (vars p) ++ (vars q) 
vars (Dis p q) = (vars p) ++ (vars q)
vars (Neg p) = vars p

-- Ejercicio 4


--4.1
conjunciones :: PL -> Int
conjunciones (Var p) = 0
conjunciones (Imp p q) = (conjunciones p) + (conjunciones q)
conjunciones (Con p q) = 1 + (conjunciones p) + (conjunciones q) 
conjunciones (Dis p q) = (conjunciones p) + (conjunciones q)
conjunciones (Neg p) = conjunciones p


--Función aupiliar que cuenta las disqunciones de una fórmula
disyunciones :: PL -> Int
disyunciones (Var p) = 0
disyunciones (Imp p q) = (disyunciones p) + (disyunciones q)
disyunciones (Con p q) = (disyunciones p) + (disyunciones q) 
disyunciones (Dis p q) = 1 + (disyunciones p) + (disyunciones q)
disyunciones (Neg p) = disyunciones p
--Función aupiliar que cuenta las implicacionees de una fórmula
imps :: PL -> Int
imps (Var p) = 0
imps (Imp p q) = 1 + (imps p) + (imps q)
imps (Con p q) = (imps p) + (imps q) 
imps (Dis p q) = (imps p) + (imps q)
imps (Neg p) = imps p
--Función aupiliar que cuenta las negaciones de una fórmula
negs :: PL -> Int
negs (Var p) = 0
negs (Imp p q) = (negs p) + (negs q)
negs (Con p q) = (negs p) + (negs q) 
negs (Dis p q) = (negs p) + (negs q)
negs (Neg p) = 1 + negs p


--Función que dependiendo un operador se cuenta el numero de apariciones 
--en una fórmula
ops :: PL -> String -> Int
ops (Var p) _ = 0
ops p "¬" = negs p
ops p "^" = conjunciones p
ops p "v" = disyunciones p
ops p "->" = imps p


-- Ejercicio 5

quitaImp :: PL -> PL
quitaImp (Var p) = Var p
quitaImp (Imp p q) = Dis (Neg (quitaImp p)) (quitaImp q)
quitaImp (Con p q) = Con (quitaImp p) (quitaImp q) 
quitaImp (Dis p q) = Dis (quitaImp p) (quitaImp q)
quitaImp (Neg p) = Neg (quitaImp p)

quitaAnd :: PL -> PL
quitaAnd (Var p) = Var p
quitaAnd (Imp p q) = Imp (quitaAnd p) (quitaAnd q)
quitaAnd (Con p q) = Neg (Dis(Neg(quitaAnd p)) (Neg(quitaAnd q))) 
quitaAnd (Dis p q) = Dis (quitaAnd p) (quitaAnd q)
quitaAnd (Neg p) = Neg (quitaAnd p)

quitaOr :: PL -> PL
quitaOr (Var p) = Var p
quitaOr (Imp p q) = Imp (quitaOr p) (quitaOr q)
quitaOr (Con p q) = Con (quitaOr p) (quitaOr q) 
quitaOr (Dis p q) = Neg (Con (Neg (quitaOr p)) (Neg (quitaOr q)) )
quitaOr (Neg p) = Neg (quitaOr p)

-- Ejercicio 6

lNand :: PL -> PL
lNand (Var p) = Var p
lNand (Imp p q) = Nand (lNand p) (Nand (lNand q) (lNand q))
lNand (Con p q) = Nand (Nand (lNand p) (lNand q) ) (Nand (lNand p) (lNand q)) 
lNand (Dis p q) = Nand (Nand (lNand p) (lNand p) ) (Nand (lNand q) (lNand q))
lNand (Neg p) = Neg (lNand p)

-- Ejercicio 7
lNor :: PL -> PL
lNor (Var p) = Var p
lNor (Imp p q) = Nor (Nor (Nor (lNor p) (lNor p)) (lNor q)) (Nor (Nor (lNor p) (lNor p)) (lNor q))
lNor (Con p q) = Nor (Nor (lNor p) (lNor p)) (Nor (lNor q) (lNor q))
lNor (Dis p q) = Nor (Nor (lNor p) (lNor q)) (Nor (lNor q) (lNor q))
lNor (Neg p) = Nor p p 


-- Ejercicio 8

satModPL :: [Variable] -> PL -> Bool -- ¿M |= phi?
-- satModPL : ConjuntoPotencia(Var) -> PL -> Bool
-- Implementa la semantica mediante modelos (subconjuntos de Var) de la PL
satModPL m phi = case phi of -- Recursivamente sobre la estructura de phi:
    -- Casos base:
    Bot               -> False
    Top               -> True
    Var x             -> x `elem` m -- ¿x es elemento de phi?
    -- Casos recursivos (coser y cantar):
    Imp alpha beta    -> not(satModPL m alpha) || (satModPL m beta)
    Dis alpha beta    -> (satModPL m alpha) || (satModPL m beta)
    Con alpha beta    -> (satModPL m alpha) && (satModPL m beta)
    Neg alpha         -> not (satModPL m alpha) 


potencia :: [a] -> [[a]]
potencia [] = [[]]
potencia (x:xs) = map (x:) (potencia xs) ++ potencia xs

