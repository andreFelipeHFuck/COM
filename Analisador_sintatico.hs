import System.IO
import Text.Parsec
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.Language
import Distribution.Simple (flagToProfDetailLevel)
import Text.Parsec.Token (GenTokenParser(identifier))
import Distribution.SPDX (License(NONE))
import Control.Applicative (Alternative(empty))
import Distribution.PackageDescription (PackageDescription(testedWith))
import Text.Read (Lexeme(String))

-- Estrutra da Árvore Sintática

type Id = String

data Type = TDouble 
            |TInt 
            |TString 
            |TVoid
            deriving Show

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
            |IdVar String -- Construtor de variavel
            |Chamada Id [Expr] 
            |Lit String
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

data Var = Id :#: Type 
           deriving Show

data Funcao = Id :->: ([Var], Type) 
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

-- Definições da linguagem
-- Configura palavras reservadas
linDef = emptyDef{
         T.commentStart = "{-",
         T.commentEnd = "-}",
         T.commentLine = "--",
         T.identStart = letter<|> char '_', 
         T.identLetter = alphaNum <|> char '_',
         T.reservedNames = ["if", "else", "return", "while", "id",
                            "print", "read", "int", "string", "double",
                            "void"]
        }

lexico = T.makeTokenParser linDef

natural = T.natural lexico
symbol = T.symbol lexico
parens = T.parens lexico
reservedOp = T.reservedOp lexico
indentifier = T.identifier lexico

semi = T.semi lexico
comma = T.comma lexico

integer = T.integer lexico
float = T.float lexico
stringLiteral = T.stringLiteral lexico
reserved = T.reserved lexico

-- Tabela de Ordem de operação
tabela   = [[prefix "-" Neg], 
            [binario "*" (:*:) AssocLeft, binario "/" (:/:) AssocLeft ],
            [binario "+" (:+:) AssocLeft, binario "-" (:-:) AssocLeft ]
           ]
tabelaL = [[prefix "!" Not],
           [binario "&" (:&:) AssocLeft],
           [binario "|" (:|:) AssocLeft]
          ]

binario name fun assoc = Infix (do{reservedOp name; return fun }) assoc
prefix name fun = Prefix (do{reservedOp name; return fun })

       
expr = buildExpressionParser tabela fator
       <?> "expression"   
        
fator = parens expr
       <|> fatorTryId
       <|> fatorTryNumeros
       <?> "simple expression"

fatorTryId = try fatorChamadaFuncao <|> fatorVariavel
fatorVariavel = do{i <- indentifier; return (IdVar i)}
fatorChamadaFuncao = do{i <- indentifier; vs <- parens (listaParametros); return (Chamada i vs)}

fatorTryNumeros = try fatorFloat <|> fatorInteiro
fatorInteiro = do {n <- natural; return (Const (CInt (fromIntegral n)))}
fatorFloat = do {f <- float; return (Const (CDouble f))}

exprR = do{e1 <- expr; o <- op; e2 <- expr; return (Rel (o e1 e2))}

op = do {reservedOp "=="; return (:==:)}
     <|> do {reservedOp "/="; return (:/=:)}
     <|> do {reservedOp "<"; return (:<:)}
     <|> do {reservedOp ">"; return (:>:)}
     <|> do {reservedOp "<="; return (:<=:)}
     <|> do {reservedOp ">="; return (:>=:)}

exprL = buildExpressionParser tabelaL fatorL 

fatorL = parens exprL
        <|> do{n <- exprR; return n}
        <?> "simple expression"

blocoPrincipal = do symbol "{"
                    bs <- blocoPrincipal'
                    symbol "}"
                    return bs

--
blocoPrincipal' = do{d <- declaracoes; l <- listaCmd; return (d, l)}

declaracoes = do{t <- tipo; i <- listaId; semi; ds <- declaracoes; return ([(x:#:t) | x <- i] ++ ds)}
              <|> return []

listaId = do{i <- indentifier; is <- listaId'; return (i:is)} 

listaId' = do{comma; listaId}
           <|> return []

-- Funçao bloco
bloco = do symbol "{"
           cs <- listaCmd
           symbol "}"
           return cs

listaCmd = do {c <- comando; cs <- listaCmd; return (c:cs)}
          <|> return []

comando = do{reserved "return"; e <- tvzExpressao; semi; return e}
          <|>do{reserved "if"; l <- parens exprL; b <- bloco; s <- senao; return (If l b s)}
          <|>do{reserved "while"; l <- parens exprL; b <- bloco; return (While l b)}
          <|>do{reserved "print"; e <- parens expr; return (Imp e)}
          <|>do{reserved "read"; i <- parens (indentifier); return (Leitura i) }
          <|>comandoTry

comandoTry = try comamndoId <|> comandoFuncao

comamndoId = do{i <- indentifier; symbol "="; e <- expr; semi; return (Atrib i e)}
comandoFuncao = do{i <- indentifier; l <- parens (listaParametros); semi; return (Proc i l)}

tvzExpressao = do{e <- expr; return (Ret (Just e))}
               <|> return (Ret (Nothing))

listaParametros = do{l <- listaParametros'; return l}
                  <|> return []

listaParametros' = do{e <- expr; l <- listaParametros''; return (e:l)}

listaParametros'' = do{comma; l <-listaParametros'; return l}
                     <|> return []

senao = do{reserved "else"; b <- bloco; return b}
        <|>do {return []}
 
tipo = do{reserved "int"; return TInt}
       <|>do{reserved "double"; return TDouble}
       <|>do{reserved "string"; return TString}

tipoRetorno = do{t <- tipo; return t}
              <|>do{reserved "void"; return TVoid}

funcao = do t <- tipoRetorno
            i <- indentifier
            p <- parens declParametros
            b <- blocoPrincipal
            return ((i :->: (p, t)), i, b)

funcoes = do{f <- funcao; fs <- funcoes; return (f:fs)}
          <|> return []

f_id (_, i, _) = i
f_fun (f, _, _) = f
f_bp_d (_, _, (d, _)) = d
f_bp_l (_, _, (_, l)) = l

funcoesListaFuncao funcoes = return [(f_fun x) | x <- funcoes]

funcoesTripla funcoes = return [( f_id x, f_bp_d x, f_bp_l x) | x <- funcoes]

parametro = do{t <- tipo; i <- indentifier; return (i:#:t)}

declParametros = do{p <- parametro; ps <- parametros; return (p:ps)}
                 <|> return []

parametros = do{comma; declParametros}
             <|> return []

programa = do f <- funcoes
              bp <- blocoPrincipal
              fl <- funcoesListaFuncao f
              fb <- funcoesTripla f
              return (Prog fl fb (fst bp) (snd bp))

partida :: Parsec String u Programa
partida = do {e <- programa; eof; return e}

parserE e = runParser partida [] "Expressoes" e

parserExpr s = case parserE s of
                     Left er -> print er
                     Right v -> (print v)
                     
main = do txt <- readFile "texto.txt"
          parserExpr txt