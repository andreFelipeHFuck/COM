import System.IO
import Analisador_sintatico
import Foreign.C (CString)

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
             |CString String
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

data VerTipo = I | D | S | V | E deriving (Eq, Show)

tipo t | t == TInt = I
       | t == TDouble = D
       | t == TString = S
       | t == TVoid = V
       | otherwise = E

varId (id :#: _) = id
varTipo (_ :#: t) = t

procIdVar _ [] = E
procIdVar id (lv: lvs) = if varId lv == id
                then tipo (varTipo lv)
                else procIdVar id lvs

funcId (id :->: _) = id
funcTipo (_ :->: (_, t)) = t
funcParamentros (_ :->: (lp, _)) = lp

procFunc id (lf:lfs) = if funcId lf == id 
                       then lf 
                       else procFunc id lfs

procIdFunc _ [] = E
procIdFunc id (lf:lfs) = if funcId lf == id 
                         then tipo (funcTipo lf)
                         else procIdFunc id lfs

constante (Const (CInt a)) = I
constante (Neg (Const (CInt a))) = I
constante (Const (CDouble a)) = D
constante (Neg (Const (CDouble a))) = D
constante (Const (CString a)) = S
constante _ = E
 
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

exprMsg (_ :+: _)  = "+"
exprMsg (_ :-: _)  = "-"
exprMsg (_ :*: _)  = "*"
exprMsg (_ :/: _)  = "/"

exprO (_ :+: _) a b = (a :+: b)
exprO (_ :-: _) a b = (a :-: b)
exprO (_ :*: _) a b = (a :*: b)
exprO (_ :/: _) a b = (a :/: b)

intParaDouble (Neg c) = Neg (IntDouble c)
intParaDouble c = IntDouble c

doubleParaInt (Neg c) = Neg (DoubleInt c)
doubleParaInt c = DoubleInt c

verExprBin expr (ta, a) (tb, b) |ta == D && tb == I = do adv "CONVERSAO DE Int PARA Double"
                                                         return (D, (exprO expr a (intParaDouble b)))
                                |ta == I && tb == D = do adv "CONVERSAO DE Int PARA Double"
                                                         return (D, (exprO expr (intParaDouble a) b))
                                |ta == D && tb == D = do return (D, (exprO expr a b))
                                |ta == I && tb == I = do return  (I, (exprO expr a b))
                                |ta == S && (tb == I || tb == D) = do erro ("OPERACAO " ++ exprMsg expr ++ " NAO ACEITA String") 
                                                                      return (E, (exprO expr a b))
                                |(ta == I || ta == D) && tb == S = do erro ("OPERACAO " ++ exprMsg expr ++ " NAO ACEITA String") 
                                                                      return (E, (exprO expr a b))
                                |ta == V || tb == V = do erro ("OPERACAO " ++ exprMsg expr ++ " NAO ACEITA PROCEDIMENTOS")
                                                         return (E, (exprO expr a b))
                                |otherwise = do return (E, (exprO expr a b)) 
                               
verExpr (Const c) _ _ = return (constante (Const c), (Const c))
verExpr (IdVar id) lv _ = return (procIdVar id lv, (IdVar id))
verExpr (Chamada id lp) _ lf = return (procIdFunc id lf, (Chamada id lp))
verExpr expr lv lf = do a <- verExpr (exprA expr) lv lf
                        b <- verExpr (exprB expr) lv lf
                        verExprBin expr a b

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

exprRMsg (_ :==: _) = "=="
exprRMsg (_ :/=: _) = "/="
exprRMsg (_ :<: _) = "<"
exprRMsg (_ :>: _) = ">"
exprRMsg (_ :<=: _) = "<="
exprRMsg (_ :>=: _) = ">="

verExprR exprR lv lf = do a <- verExpr (exprRA exprR) lv lf
                          b <-  verExpr (exprRB exprR) lv lf
                          if fst a == D && fst b == I
                             then return (exprRO exprR (snd a) (intParaDouble (snd b)))
                          else if fst a == I && fst b == D 
                               then return (exprRO exprR (intParaDouble (snd a)) (snd b)) 
                          else if fst a == S && (fst b == I || fst b == D)
                               then do erro ("OPERACAO " ++ exprRMsg exprR ++ " SO ACEITA String NOS DOIS LADOS")
                                       return (exprRO exprR (snd a) (snd b))
                          else if (fst a == I || fst a == D) && fst b == S
                                then do erro ("OPERACAO " ++ exprRMsg exprR ++ " SO ACEITA String NOS DOIS LADOS")
                                        return (exprRO exprR (snd a) (snd b))
                          else if fst a == V || fst b == V 
                                then do erro ("OPERACAO " ++ exprRMsg exprR ++ " NAO ACEITA PROCEDIMENTOS")
                                        return (exprRO exprR (snd a) (snd b))
                          else return (exprRO exprR (snd a) (snd b))
                            

exprLA (a :&: _) = a
exprLA (a :|: _) = a

exprLB (_ :&: b) = b
exprLB (_ :|: b) = b

exprLO (_ :&: _) a b = (a :&: b)
exprLO (_ :|: _) a b = (a :|: b)

verExprL (Rel exprR) lv lf = do vr <- verExprR exprR lv lf
                                return (Rel vr)
verExprL (Not (Rel exprR)) lv lf = do vr <- verExprR exprR lv lf
                                      return (Not (Rel vr))
verExprL (Not exprL) lv lf = do a <- verExprL (exprLA exprL) lv lf
                                b <- verExprL (exprLB exprL) lv lf
                                return (Not ((exprLO exprL a b)))                           
verExprL exprL lv lf = do a <- verExprL (exprLA exprL) lv lf
                          b <- verExprL (exprLB exprL) lv lf 
                          return (exprLO exprL a b)

verComando' [] [] lv lf = return []
verComando' (e:es) (p:ps) lv fs = do ve <- verExpr e lv fs
                                     ves <- verComando' es ps lv fs
                                     if fst ve == I && vp == D
                                        then return ((intParaDouble (snd ve)):ves)
                                     else if fst ve == D && vp == I
                                        then return ((doubleParaInt (snd ve)):ves)
                                     else return ((snd ve):ves)                                    
                                     where
                                          vp = tipo (varTipo p)
                                 
--  Ret (Maybe Expr)
verComando (If exprL b1 b2) lv lf = do vL <- verExprL exprL lv lf 
                                       vb1 <- verBloco b1 lv lf
                                       vb2 <- verBloco b2 lv lf
                                       return ( If vL vb1 vb2)
verComando (While exprL b) lv lf = do vL <- verExprL exprL lv lf
                                      vb <- verBloco b lv lf
                                      return (While vL vb)

verComando (Atrib id expr) lv lf = do v <- verExpr expr lv lf
                                      if fst v == I && procIdVar id lv == D 
                                         then return (Atrib id (intParaDouble (snd v)))
                                      else if fst v == D && procIdVar id lv == I
                                         then return (Atrib id (doubleParaInt (snd v)))
                                      else return (Atrib id (snd v))

verComando (Leitura id) _ _ = return (Leitura id)
verComando (Imp expr) lv lf = do v <- verExpr expr lv lf
                                 return (Imp (snd v))

-- Para retorno de Função precisa da tripla
verComando (Ret (Just expr)) lv lf = do v <- verExpr expr lv lf
                                        return (Ret (Just (snd v)))

verComando (Ret Nothing) _ _ = return (Ret Nothing)

verComando (Proc id lExpr) lv fs = do lvExpr <- verComando' lExpr lp lv fs
                                      return (Proc id lvExpr)
                                      where 
                                           f = procFunc id fs
                                           lp = funcParamentros f
                                       
verBloco [] lv lf = return []
verBloco (b:bs) lv lf = do vb <- (verComando b lv lf)
                           vbs <- (verBloco bs lv lf)
                           return (vb:vbs)

    


semantico (Prog fs lf lv b) = do vb <- verBloco b lv fs
                                 return (Prog fs lf lv vb)


