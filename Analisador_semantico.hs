import System.IO
import Analisador_sintatico
import Text.XHtml (base)

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

data VerTipo = I | D | N deriving (Eq, Show)

varId (id :#: _) = id
varTipo (_ :#: t) = t

varTipo' t | t == TInt = I
           | t == TDouble = D
           | otherwise = N

procIdVar _ [] = N
procIdVar id (lv: lvs) = if varId lv == id
                then varTipo' (varTipo lv)
                else procIdVar id lvs

isIdVar (IdVar _) = True
isIdVar _ = False

idVar (IdVar id) = id
 
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

exprO (_ :+: _) a b = (a :+: b)
exprO (_ :-: _) a b = (a :-: b)
exprO (_ :*: _) a b = (a :*: b)
exprO (_ :/: _) a b = (a :/: b)

constante (Const (CInt a)) = I
constante (Neg (Const (CInt a))) = I
constante (Const (CDouble a)) = D
constante (Neg (Const (CDouble a))) = D
constante _ = N

isConst (Const _) = True
isConst (Neg (Const _)) = True
isConst _ = False

intParaDouble (Neg c) = Neg (IntDouble c)
intParaDouble c = IntDouble c

verExprBin expr (ta, a) (tb, b) |ta == D && tb == I = (D, (exprO expr a (intParaDouble b)))
                                |ta == I && tb == D = (D, (exprO expr (intParaDouble a) b))
                                |ta == D && tb == D = (D, (exprO expr a b))
                                |ta == I && tb == I = (I, (exprO expr a b))
                               
verExpr (Const c) _ = (constante (Const c), (Const c))
verExpr (IdVar id) lv = (procIdVar id lv, (IdVar id))
verExpr expr lv = verExprBin expr a b
                 where 
                      a = verExpr (exprA expr) lv
                      b = verExpr (exprB expr) lv

exprRA (a :==: _) = a
exprRA (a :/=: _) = a
exprRA (a :<: _) = a
exprRA (a :>: _) = a
exprRA (a :<=: _) = a
exprRA (a :>=: _) = a

exprRB (_ :==:b) = b
exprRB (_ :/=:b) = b
exprRB (_ :<: b) = b
exprRB (_ :>: b) = b
exprRB (_ :<=:b) = b
exprRB (_ :>=:b) = b

exprRO (_ :==: _) a b = (a :==: b)
exprRO (_ :/=: _) a b = (a :/=: b)
exprRO (_ :<: _) a b = (a :<: b)
exprRO (_ :>: _) a b = (a :>: b)
exprRO (_ :<=: _) a b = (a :<=: b)
exprRO (_ :>=: _) a b = (a :>=: b)

verExprR exprR lv | fst a == D && fst b == I = exprRO exprR (snd a) (intParaDouble (snd b))
                  | fst a == I && fst b == D = exprRO exprR (intParaDouble (snd a)) (snd b)
                  | otherwise = exprRO exprR (snd a) (snd b)
                   where 
                         a = verExpr (exprRA exprR) lv
                         b = verExpr (exprRB exprR) lv

-- lf = do sint <- analisadorSintatico
--         let l = listaFuncoes sint 
--         return l

teste = do sint <- analisadorSintatico
           let m = MS("Teste", sint)
           return m

