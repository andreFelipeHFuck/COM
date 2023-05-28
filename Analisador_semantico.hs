import System.IO
import Analisador_sintatico

-- Monada Semantica

data Semantica a = MS (String, a) 
                   deriving Show

instance Functor Semantica where
         fmap f (MS (s, a)) = MS(s, f a)

instance Applicative Semantica where
    pure x = MS(" ", x)
    MS(s1, f) <*> MS(s2, x) = MS(s1 <> s2, f x)

instance Monad Semantica where
    MS(s, a) >>= f = let MS(s', b) = f a in MS (s++s', b)

-- Estrutura da Arvore Sintatica
type Id = String

data Tipo = TDouble 
            |TInt 
            |TString 
            |TVoid
            deriving (Eq, Show)

data TCons = CDouble Double 
             |CInt Int 
             deriving Show

data Expr = Expr :+: Expr 
            |Expr :-: Expr 
            |Expr :*: Expr 
            |Expr :/: Expr 
            |Neg Expr 
            |Const TCons 
            |IdVar Id 
            |Chamada Id [Expr] 
            |Lit String 
            |IntDouble Expr 
            |DoubleInt Expr 
            deriving Show

data ExprR = Expr :==: Expr 
             |Expr :/=: Expr 
             |Expr :<: Expr 
             |Expr :>: Expr 
             |Expr :<=: Expr 
             |Expr :>=: Expr 
             deriving Show

data ExprL = ExprL :&: ExprL 
            |ExprL :|: ExprL 
            |Not ExprL 
            |Rel ExprR
            deriving Show

data Var = Id :#: Tipo 
           deriving (Eq, Show)

data Funcao = Id :->: ([Var], Tipo) 
              deriving Show     

data Programa = Prog [Funcao] [(Id, [Var], Bloco)] [Var] Bloco
                deriving Show

type Bloco = [Comando]

data Comando = If ExprL Bloco Bloco
                |While ExprL Bloco
                |Atrib Id Expr
                |Leitura Id
                |Imp Expr
                |Ret (Maybe Expr)
                |Proc Id [Expr]
                deriving Show

erro s = MS ("Erro: " ++ s, ())
adv s = MS ("Advertencia: " ++ s, ())

listaFuncoes (Prog fs _ _ _) = fs
defFuncoes (Prog _ lf _ _) = lf
listaVariaveis (Prog _ _ lv _) = lv
bloco (Prog _ _ _ b) = b

varId (id :#: _) = id
varTipo (_ :#: t) = t

procIdVar _ [] = TVoid
procIdVar id (lv: lvs) = if varId lv == id
                then varTipo lv
                else procIdVar id lvs

isIdVar (IdVar _) = True
isIdVar _ = False

idVar (IdVar id) = id
 
constTipo (Const t) = t

constante (Const (CInt a)) = True
constante (Neg (Const (CInt a))) = True
constante (Const (CDouble a)) = False
constante (Neg (Const (CDouble a))) = False
constante _ = False


-- constante' (a :+: b) = constante a && constante b
constante' ((Const (CInt _)) :+: (Const (CInt _)) ) = True
constante' ((IntDouble _) :+: (_) ) = False
constante' ((_) :+: (IntDouble _) ) = False
constante' _ = False

intParaDouble (Neg c) = Neg (IntDouble c)
intParaDouble c = IntDouble c

varA (a :+: b) lv | procIdVar (idVar a) lv == TInt && not(constante b) = (intParaDouble a :+: b)
                  | procIdVar (idVar a) lv == TDouble && constante b = (a :+: intParaDouble b)
                  | otherwise = (a :+: b)

varB (a :+: b) lv | not(constante a) && procIdVar (idVar b) lv == TInt = (a :+: intParaDouble b)
                  | constante a && procIdVar (idVar b) lv == TDouble = (intParaDouble a :+: b)
                  | otherwise = (a :+: b)

verVar (a :+: b) lv | procIdVar (idVar a) lv == TInt && procIdVar (idVar b) lv == TDouble = (intParaDouble a :+: b)
                    | procIdVar (idVar a) lv == TDouble && procIdVar (idVar b) lv == TInt = (a :+:  intParaDouble b)
                    | otherwise = (a :+: b)

verificaExprBinaria (a :+: b) lv | isIdVar a && isIdVar b = verVar (a :+: b) lv
                                 | isIdVar a = varA (a :+: b) lv
                                 | isIdVar b = varB (a :+: b) lv
                                 | constante a && constante b == False = ((intParaDouble a) :+: b)
                                 | constante a == False && constante b = (a :+: (intParaDouble b))
                                 | constante a == False && constante' b = intParaDouble (a :+: b)
                                 | constante' a && constante b == False = intParaDouble (a :+: b)
                                 | constante' a && constante' b == False = ((intParaDouble a) :+: b)
                                 | constante' a == False && constante' b = (a :+: (intParaDouble b))
                                 | otherwise = (a :+: b)

exprA (a :+: _) = a
exprA (a :-: _) = a
exprA (a :*: _) = a
exprA (a :/: _) = a
exprA a = a

exprB (_ :+: b) = b
exprB (_ :-: b) = b
exprB (_ :*: b) = b
exprB (_ :/: b) = b
exprB b = b

verificaExpr' (Const (_) :+: Const (_)) = True
verificaExpr' (Const (_) :-: Const (_)) = True
verificaExpr' (Const (_) :*: Const (_)) = True
verificaExpr' (Const (_) :/: Const (_)) = True
verificaExpr' (Const (_)) = True
verificaExpr' (_ :+: _) = False     
verificaExpr' (_ :-: _) = False     
verificaExpr' (_ :*: _) = False   
verificaExpr' (_ :/: _) = False    

verificaExpr'' (Const (_)) = False
verificaExpr'' (_) = True

verificaExpr expr lv | verificaExpr' expr =  verificaExprBinaria ((exprA expr) :+: (exprB  expr)) lv
                     | not(verificaExpr' (exprA expr)) = ((verificaExprBinaria (verificaExpr (exprA expr) lv) lv) :+: (exprB expr))
                     | not(verificaExpr' (exprB expr)) = ((exprA expr) :+: (verificaExprBinaria(verificaExpr (exprB expr) lv) lv))
                     | verificaExpr' (exprA expr) = ((verificaExprBinaria (verificaExpr (exprA expr) lv) lv) :+: (exprB expr))
                     | verificaExpr' (exprB expr) = ((exprA expr) :+: (verificaExprBinaria(verificaExpr (exprB expr) lv) lv))

-- verExpr (Const (CInt 1) :+: (IdVar "a" :+: IdVar "b")) ["a" :#: TInt,"c" :#: TInt,"b" :#: TDouble]
verExpr (Const a) _ = (Const a)
verExpr (IdVar a) _ = (IdVar a)
verExpr (Const a :+: Const b) lv = verificaExprBinaria (Const (a) :+: Const (b)) lv
verExpr expr lv = verificaExprBinaria ((verExpr (exprA expr) lv) :+: (verExpr (exprB expr) lv)) lv

               
-- lf = do sint <- analisadorSintatico
--         let l = listaFuncoes sint 
--         return l

teste = do sint <- analisadorSintatico
           let m = MS("Teste", sint)
           return m


