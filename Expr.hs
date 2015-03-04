module Expr where
import Control.Applicative hiding ((<|>), many)
import Text.Parsec
import Text.Parsec.Prim (getPosition)
import Text.Parsec.Pos (SourcePos)
import Text.Parsec.Token

type Loc = SourcePos
type Var = String
data Expr = Var Loc Var
          | Lam Loc Var Expr
          | App Loc Expr Expr

instance Show Expr where
  show (Var l s)     = s
  show (Lam l s e)   = "λ" ++ s  ++ "." ++ show e
  show (App l e1 e2) = "(" ++ show e1 ++ " " ++ show e2 ++ ")" 

instance Ord Expr where
  e `compare` e' = loc e `compare` loc e'

instance Eq Expr where
  e == e' = loc e == loc e'

loc e = case e of
  Var l v -> l
  Lam l v e -> l
  App l m n -> l
lam = char '\\' <|> char 'λ'
var = many1 letter
pa <^> pb = pa <* spaces <*> pb 
pa ^> pb  = (pa >> spaces) *> pb
pa <^ pb  = pa <* (spaces >> pb)
infixl 4 <^>, <^, ^>

parseExpr = parse expr where
  expr :: Parsec String () Expr
  expr =  Lam <$> getPosition <*> ((lam *> var) <* char '.') <^> expr 
      <|> App <$> getPosition <*> (char '(' ^> expr) <^> (expr <^ char ')') 
      <|> Var <$> getPosition <*> var
      <|> char '{' ^> (lets <$> many (spaces *> binding <* spaces) <^> (char '}' ^> expr))
        where lets = flip $ foldr ($) 
              binding = mylet <$> getPosition <*> var <^> (getPosition <* char '=') <^> expr
              mylet l2 var l1 term body = App l1 (Lam l2 var body) term
