import System.IO
import Data.List
import Analisador_sintatico

-- Monada Semantica

data Semantica a = MS (String, a) 
                   deriving Show

instance Functor Semantica where
         fmap f (MS (s, a)) = MS(s, f a)

instance Applicative Semantica where
    pure x = MS("", x)
    MS(s1, f) <*> MS(s2, x) = MS(s1 <> s2, f x)

instance Monad Semantica where
    MS(s, a) >>= f = let MS(s', b) = f a in MS (s++s', b)

red = "\x1b[31m"
yellow = "\x1b[33m"
reset = "\x1b[0m"

erro s = MS (red ++ "Erro: " ++ reset ++ s ++ "\n", ())
adv s = MS (yellow ++ "Advertencia: " ++ reset ++ s ++ "\n", ())

data VerTipo = I | D | S | V | E deriving (Eq, Show)

printTipo I = "Int"
printTipo D = "Double"
printTipo S = "String"
printTipo V = "Void"

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

listaFuncId (id, _, _) = id
listaFuncVar (_, var, _) = var
listaFuncBloco (_, _, bloco) = bloco 

procFunc id (fs:fss) = if funcId fs == id 
                       then fs 
                       else procFunc id fss

procIdFunc _ [] = E
procIdFunc id (fs:fss) = if funcId fs == id 
                         then tipo (funcTipo fs)
                         else procIdFunc id fss

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

verExprBin expr (ta, a) (tb, b) |ta == D && tb == I = do adv "Conversao de Int para Double"
                                                         return (D, (exprO expr a (intParaDouble b)))
                                |ta == I && tb == D = do adv "Conversao de Int para Double"
                                                         return (D, (exprO expr (intParaDouble a) b))
                                |ta == D && tb == D = do return (D, (exprO expr a b))
                                |ta == I && tb == I = do return  (I, (exprO expr a b))
                                |ta == S && (tb == I || tb == D) = do erro ("Operacao " ++ exprMsg expr ++ " nao aceita String nos seus operadores") 
                                                                      return (tb, (exprO expr a b))
                                |(ta == I || ta == D) && tb == S = do erro ("Operacao " ++ exprMsg expr ++ " nao aceita String nos seus operadores") 
                                                                      return (ta, (exprO expr a b))
                                |ta == V || tb == V = do erro ("Operacao " ++ exprMsg expr ++ " nao aceita procedimentos nos seus operadores")
                                                         return (E, (exprO expr a b))
                                |otherwise = do return (E, (exprO expr a b)) 
                               
verExpr (Const c) _ _ = return (constante (Const c), (Const c))

verExpr (IdVar id) lv _ = do if varTipo == E 
                             then do erro("O identidicaro '" ++ id ++ "' esta indefinido")
                                     return (E, (IdVar id))
                             else return (varTipo, (IdVar id))
                          where 
                               varTipo = procIdVar id lv

verExpr (Chamada id lp) _ fs = do if funcTipo == E
                                     then do erro ("Referencia indefinida para '" ++ id ++ "'")
                                             return (E, (Chamada id lp))
                                  else return (funcTipo, (Chamada id lp))
                               where 
                                     funcTipo = procIdFunc id fs
verExpr expr lv fs = do a <- verExpr (exprA expr) lv fs
                        b <- verExpr (exprB expr) lv fs
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

verExprR exprR lv fs = do a <- verExpr (exprRA exprR) lv fs
                          b <-  verExpr (exprRB exprR) lv fs
                          if fst a == D && fst b == I
                             then return (exprRO exprR (snd a) (intParaDouble (snd b)))
                          else if fst a == I && fst b == D 
                               then return (exprRO exprR (intParaDouble (snd a)) (snd b)) 
                          else if fst a == S && (fst b == I || fst b == D)
                               then do erro ("Operacao " ++ exprRMsg exprR ++ " so aceita String se estiver nos dois operadores")
                                       return (exprRO exprR (snd a) (snd b))
                          else if (fst a == I || fst a == D) && fst b == S
                                then do erro ("Operacao " ++ exprRMsg exprR ++ " so aceita String se estiver nos dois operadores")
                                        return (exprRO exprR (snd a) (snd b))
                          else if fst a == V || fst b == V 
                                then do erro ("Operacao " ++ exprRMsg exprR ++ " so aceita String se estiver nos dois operadores")
                                        return (exprRO exprR (snd a) (snd b))
                          else return (exprRO exprR (snd a) (snd b))
                            

exprLA (a :&: _) = a
exprLA (a :|: _) = a

exprLB (_ :&: b) = b
exprLB (_ :|: b) = b

exprLO (_ :&: _) a b = (a :&: b)
exprLO (_ :|: _) a b = (a :|: b)

verExprL (Rel exprR) lv fs = do vr <- verExprR exprR lv fs
                                return (Rel vr)
verExprL (Not (Rel exprR)) lv fs = do vr <- verExprR exprR lv fs
                                      return (Not (Rel vr))
verExprL (Not exprL) lv fs = do a <- verExprL (exprLA exprL) lv fs
                                b <- verExprL (exprLB exprL) lv fs
                                return (Not ((exprLO exprL a b)))                           
verExprL exprL lv fs = do a <- verExprL (exprLA exprL) lv fs
                          b <- verExprL (exprLB exprL) lv fs
                          return (exprLO exprL a b)


elemExiste  _ i [] = False
elemExiste f id (e:es) |f id == f e = True
                       |otherwise = elemExiste f id es

verAtrib' (Atrib id expr) lv fs = do v <- verExpr expr lv fs
                                     return (Atrib id (snd v))

verAtrib (Atrib id expr) lv fs = do v <- verExpr expr lv fs
                                    if fst v == I && var == D 
                                       then do adv ("Conversao de Int para Double em '" ++ id ++ "'")
                                               return (Atrib id (intParaDouble (snd v)))
                                    else if fst v == D && var == I
                                        then do adv ("Conversao de Double para Int em '" ++ id ++ "'")
                                                return (Atrib id (doubleParaInt (snd v)))
                                    else if fst v == S && var /= S
                                        then do erro ("A variavel '" ++ id ++ "' do tipo " ++ tipo ++ " nao pode ser atribuida com o tipo " ++ printTipo (fst v))
                                                return (Atrib id (snd v))
                                    else return (Atrib id (snd v))
                                 where 
                                        var = procIdVar id lv
                                        tipo = printTipo var

verRet (Ret (Just expr)) t lv fs = do v <- verExpr expr lv fs
                                      if fst v == I && t == D
                                        then do adv "Conversao de Int para Double "
                                                return (Ret (Just (intParaDouble (snd v))))
                                        else if fst v == D && t == I
                                             then do adv "Conversao de Double para Int "
                                                     return (Ret (Just (doubleParaInt (snd v))))
                                        else if fst v /= t
                                             then do erro ("Tipo do retorno icompativel")
                                                     return (Ret (Just expr))
                                        else return (Ret (Just expr))

verProc' (Proc id lExpr) lv fs = do if length lExpr == length numP
                                      then do vlExpr <- verProc lExpr lp lv fs
                                              return (Proc id vlExpr)
                                      else if length lExpr > length numP
                                          then do erro ("Excesso de argumentos na funcao " ++ id ++ " ")
                                                  return (Proc id lExpr)
                                      else do erro ("Muito poucos argumento na chamada de funcao '" ++ id ++ "'")
                                              return (Proc id lExpr) 
                                      where 
                                           f = procFunc id fs
                                           lp = funcParamentros f
                                           numP = funcParamentros (procFunc id fs)

verProc [] [] lv fs = return []
verProc (e:es) (p:ps) lv fs = do ve <- verExpr e lv fs
                                 ves <- verProc es ps lv fs
                                 if fst ve == I && vp == D
                                    then return ((intParaDouble (snd ve)):ves)
                                 else if fst ve == D && vp == I
                                     then return ((doubleParaInt (snd ve)):ves)
                                 else return ((snd ve):ves)                                    
                                 where
                                      vp = tipo (varTipo p)

verComando (If exprL b1 b2) t lv fs = do vL <- verExprL exprL lv fs
                                         vb1 <- verBloco b1 t lv fs
                                         vb2 <- verBloco b2 t lv fs
                                         return ( If vL vb1 vb2)

verComando (While exprL b) t lv fs = do vL <- verExprL exprL lv fs
                                        vb <- verBloco b t lv fs
                                        return (While vL vb)

verComando (Atrib id expr) _ lv fs = if elemExiste varId var lv
                                    then do v <- verAtrib atr lv fs
                                            return v
                                    else do erro ("O identidicador '" ++ id ++ "' esta indefinido")
                                            v' <- verAtrib' atr lv fs
                                            return v'
                                    where 
                                         atr = (Atrib id expr)
                                         var = (id :#: TVoid)
                                      
verComando (Leitura id) _ _ _ = return (Leitura id)
verComando (Imp expr) _ lv fs = do v <- verExpr expr lv fs
                                   return (Imp (snd v))

-- Para retorno de Função precisa da tripla
verComando (Ret (Just expr)) t lv fs = do v <- verRet r t lv fs
                                          return v
                                       where 
                                             r = (Ret (Just expr))

verComando (Ret Nothing) t _ _ = do if t /= V
                                    then do erro ("Tipo de retorno incompativel")
                                            return (Ret Nothing)
                                    else return (Ret Nothing)

verComando (Proc id lExpr) _ lv fs = do if f == E
                                        then do erro ("A funcao '" ++ id ++ "' nao esta definida")
                                                return prc
                                        else do v <- verProc' prc lv fs
                                                return v
                                        where 
                                             prc = (Proc id lExpr)
                                             f = procIdFunc id fs
                                       
verBloco :: Bloco -> VerTipo -> [Var] -> [Funcao] -> Semantica Bloco
verBloco [] _ _ _ = return []
verBloco (b:bs) t lv fs = do vb <- (verComando b t lv fs)
                             vbs <- (verBloco bs t lv fs)
                             return (vb:vbs)

verReptFunc [] = (False, "")
verReptFunc (fs:fss) |elemExiste funcId fs fss = (True, funcId fs)
                     |otherwise = verReptFunc fss

verReptVar [] = (False, "")
verReptVar (lv:lvs) |elemExiste varId lv lvs = (True, varId lv)
                    |otherwise = verReptVar lvs

verReptFuncParametro [] = return True
verReptFuncParametro (fs:fss) = do let v = verReptVar (funcParamentros fs)
                                   if fst v
                                   then do erro ("O parametro '" ++ snd v ++ "' foi declarado mais de uma vez")
                                           return False
                                   else return True

verFuncoes fs = do let f = verReptFunc fs
                   if fst f
                   then do erro("A funcao '" ++ snd f ++ "' foi declarada mais de uma vez")
                           return False
                   else return True

verVariaveis lv = do let v = verReptVar lv
                     if fst v
                     then do erro ("A variavel '" ++ snd v ++ "' foi declarada mais de uma vez")
                             return False
                     else return True                 

verFuncao f fs = do vlv <- verVariaveis lv
                    if vlv
                    then do vb <- verBloco b t lv fs
                            return (id, lv, vb)
                    else return f
                 where 
                      id = listaFuncId f
                      t = procIdFunc id fs
                      lv = (listaFuncVar f) ++ (funcParamentros (procFunc id fs))
                      b = listaFuncBloco f

verListaFuncoes [] _ = return []
verListaFuncoes (lf:lfs) fs = do vlf <- (verFuncao lf fs)
                                 vlfs <- (verListaFuncoes lfs fs)
                                 return (vlf:vlfs)
                        
semantico (Prog fs lf lv b) = do vfs <- verFuncoes fs
                                 vlp <- verReptFuncParametro fs
                                 vlv <- verVariaveis lv
                                 if vfs && vlv 
                                 then do 
                                        vb <- verBloco b V lv fs
                                        vlf <- verListaFuncoes lf fs
                                        return (Prog fs vlf lv vb)
                                 else return (Prog fs lf lv b)

printSemantica' p = do putStrLn (fst p)
                       print (snd p)

printSemantica p = do let sem = semantico p
                      case sem of
                        MS p -> printSemantica' p

main = do input <- readFile "texto.txt"
          let sin = parserE input
          case sin of 
                Left er -> print er
                Right v -> printSemantica v
          
        