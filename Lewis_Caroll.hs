data Formule = Var String
   | Non Formule
   | Et Formule Formule
   | Ou Formule Formule
   | Imp Formule Formule
   | Equi Formule Formule
      deriving (Eq, Show)

-- Exemples
f1 = (Ou (Et (Var "c") (Var "d")) (Et (Var "a") (Var "b")))
f2 = (Imp (Var "d") (Ou (Var "c") (Non (Var "b"))))
f2b = (Imp (Non (Var "d")) (Ou (Var "c") (Var "b")))
f3 = (Equi (Var "d") (Et (Var "c") (Var "d")))
f4 = (Imp (Non (Var "d")) (Ou (Var "c") (Var "b")))
f5 = (Non (Non (Var "a")))
f6 = (Imp (Non (Ou (Var "a") (Var "d"))) (Ou (Var "c") (Var "b")))

exemple1 = (Et (Imp (Var "A") (Var "B"))
               (Et (Imp (Var "B") (Var "C"))
                  (Et (Imp (Var "C") (Non (Var "D")))
                    (Et (Imp (Non (Var "D")) (Non (Var "E")))
                       (Imp (Non (Var "E")) (Var "F"))))))


exemple2 = (Et (Imp (Non (Var "A")) (Var "B"))
             (Et (Imp (Var "C") (Non (Var "D")))
                 (Et (Imp (Var "E") (Non (Var "F")))
                     (Et (Imp (Non (Var "D")) (Non (Var "B")))
                         (Imp (Var "A") (Var "F"))))))


bebe = (Et (Imp (Var "bebe") (Non (Var "logique")))
          (Et (Imp (Var "tuer crocodile") (Non (Var "meprise")))
             (Imp (Non (Var "logique")) (Var "meprise"))))


a1 = "les sains d_esprit"
b1 = "possibles logiciens"
c1 = "enfants"
d1 = "malade mental"
g1 = "juge possible"

logiciens = (Et (Imp (Var a1) (Var b1))
               (Et (Imp (Var g1) (Non (Var d1)))
                  (Et (Imp (Var b1) (Non (Var c1)))
                      (Imp (Non (Var d1)) (Var a1)))))

a2 = "les eleves de moins de 12 ans"
b2 = "interne"
c2 = "les eleves studieux"
d2 = "cheveux roux"
e2 = "helleniste"
g2 = "paresseux"
h2 = "externe"

ecole = (Et (Imp (Var b2) (Non (Var a2)))
            (Et (Imp (Var c2) (Var d2))
                (Et (Imp (Var e2) (Non (Var h2)))
                     (Et (Imp (Non (Var a2)) (Non (Var g2)))
                         (Et (Imp (Non (Var h2)) (Var b2))
                             (Imp (Non (Var g2)) (Var c2)))))))




-- Visualisation de la formule
visuFormule :: Formule -> String
visuFormule (Var p) = p
visuFormule (Non f) = "~" ++ (visuFormule f)
visuFormule (Et g d) = "(" ++ (visuFormule g) ++ " & " ++ (visuFormule d) ++ ")"
visuFormule (Ou g d) = "(" ++ (visuFormule g) ++ " v " ++ (visuFormule d) ++ ")"
visuFormule (Imp g d) = "(" ++ (visuFormule g) ++ " => " ++ (visuFormule d) ++ ")"
visuFormule (Equi g d) = "(" ++ (visuFormule g) ++ " <=> " ++ (visuFormule d) ++ ")"

-- Enlève tous les implications et équivalence de la formule
elimine :: Formule -> Formule
elimine (Var p) = (Var p)
elimine (Non f) = (Non (elimine f))
elimine (Et g d) = (Et (elimine g) (elimine d))
elimine (Ou g d) = (Ou (elimine g) (elimine d))
elimine (Imp g d) = (Ou (Non (elimine g)) (elimine d))
elimine (Equi g d) = (Et (elimine (Imp g d)) (elimine (Imp d g)) )

-- Amène les négations devant les littéraux positifs
ameneNon, disNon :: Formule -> Formule
ameneNon (Var p) = (Var p)
ameneNon (Non f) = disNon f
ameneNon (Et g d) = (Et (ameneNon g) (ameneNon d))
ameneNon (Ou g d) = (Ou (ameneNon g) (ameneNon d))

-- Renvoie la négation de la formule pour appliquer les 2 lois de Morgan
disNon (Var p) = (Non (Var p))
disNon (Non f) = ameneNon f
disNon (Et g d) = (Ou (disNon g) (disNon d))
disNon (Ou g d) = (Et (disNon g) (disNon d))

-- Les fonctions permettent de faire développer la formule
normalise :: Formule -> Formule
normalise (Et g d) = concEt (normalise g) (normalise d)
normalise (Ou g d) = developper (normalise g) (normalise d)
normalise f = f

concEt :: Formule -> Formule -> Formule
concEt (Et g d) f = (Et g (concEt d f))
concEt g f = (Et g f)

developper :: Formule -> Formule -> Formule
developper (Et g1 g2) d = normalise (Et (Ou g1 d) (Ou g2 d))
developper g (Et d1 d2) = normalise (Et (Ou g d1) (Ou g d2))
developper g d = (Ou g d)

-- Utilise les fonctions pour être sous forme clausale
-- (Application de l'algèbre de Boole)
formeClausale :: Formule -> Formule
formeClausale f = normalise (ameneNon (elimine f))


type Clause = [Formule] -- Une liste de littéraux
type FormuleBis = [Clause] -- Une liste de Clause

-- Fonction pour transformé la formule en une liste de Clause
etToListe :: Formule -> FormuleBis
etToListe (Et g d) = (ouToListe g) : (etToListe d)
etToListe f = [(ouToListe f)]

-- Fonction pour transformé la formule en une liste de littéraux
ouToListe :: Formule -> Clause
ouToListe (Ou g d) = g : (ouToListe d)
ouToListe f = [f]

-- Fonction qui associe la négation de la formule
neg :: Formule -> Formule
neg (Var v) = (Non (Var v))
neg (Non (Var v)) = (Var v)

-- Fonction pour savoir un littéral dans une Clause à un littéral
-- négatif dans l'autre Clause
sontLiees :: Clause -> Clause -> Bool
sontLiees [] _ = False
sontLiees (x:xs) ys
    | ys == [] = False
    | x == (neg (head ys)) = True
    | otherwise = (sontLiees xs ys) || (sontLiees (x:xs) (tail ys))

resolvante :: Clause -> Clause -> Clause
resolvante [] _ = []
resolvante _ [] = []
resolvante (x:xs) (y:ys)
    --Nous pouvons mettre la partie qui est en commentaire, cela fonctionnera encore
    {- | x == y && ys /= [] && xs /= [] && (tail xs) /= [] && (head xs) == (neg (head ys))
    && (head (tail xs)) == y                            = (tail xs) ++ (tail ys) -}
    | x == y && (sontLiees xs [y])                      = resolvante xs (y:ys)
    | x == y                                            = resolvante (x:xs) ys
    {- | xs /= [] && (head xs) == (neg y) && (tail xs) /= [] && ys /= []
    && x == (head ys) && (head (tail xs)) == x          = (tail xs) ++ (tail ys)
    | ys /= [] && (tail ys) /= [] && (head ys) == (neg x) && xs /= []
    && y == (head xs) && (head (tail ys)) == y          = xs ++ (tail (tail ys)) -}
    | x == (neg y)                                      = xs ++ ys
    | (sontLiees xs [y]) && ys /= [] && x == (head ys)  = x : (resolvante xs (y:(tail ys)))
    | (sontLiees [x] ys) && xs /= [] && y == (head xs)  = y : (resolvante (x:(tail xs)) ys)
    | (sontLiees xs [y])                                = x : (resolvante xs (y:ys))
    | (sontLiees [x] ys)                                = y : (resolvante (x:xs) ys)
    | otherwise                                         = x : y : (resolvante xs ys)

-- Résoud les formules de Lewis Caroll, conclusion du sorite
deduire :: Formule -> Clause
deduire x = resoudre (head sorite) (tail sorite)
    where sorite = (etToListe (formeClausale x))

resoudre :: Clause -> FormuleBis -> Clause
resoudre xs [] = xs
resoudre xs (ys:yss)
    | sontLiees xs ys = resoudre (resolvante xs ys) yss
    | otherwise = resoudre xs (yss ++ [ys])

